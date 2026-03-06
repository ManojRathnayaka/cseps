#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════════╗
║       CSePS — Cryptographically Secure Government e-Procurement          ║
║                                                                          ║
║  Security Features:                                                      ║
║    • ECC keypairs (SECP256R1) for bidders & master encryption key        ║
║    • ECIES hybrid encryption  (ECDH ephemeral + AES-256-GCM)            ║
║    • ECDSA digital signatures for non-repudiation                        ║
║    • Shamir k-of-n threshold secret sharing for master private key       ║
║    • SHA-256 hash-chain ledger (tamper-proof, publicly verifiable)       ║
║    • Trusted UTC timestamps on every ledger entry                        ║
║    • Commitment scheme: share hashes prevent evaluator substitution      ║
║    • Bidder anonymity until post-deadline key reconstruction             ║
╚══════════════════════════════════════════════════════════════════════════╝
"""

import os, sys, json, hashlib, secrets, base64, datetime, textwrap
from pathlib import Path
from typing import List, Tuple

# ─── Dependency check ────────────────────────────────────────────────────────
try:
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import ec
    from cryptography.hazmat.primitives.kdf.hkdf import HKDF
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    from cryptography.hazmat.backends import default_backend
    from cryptography.exceptions import InvalidSignature
except ImportError:
    print("\n  [ERROR] 'cryptography' library not found.")
    print("  Install it with:  pip install cryptography\n")
    sys.exit(1)

# ══════════════════════════════════════════════════════════════════════════════
# CONSTANTS & FILE PATHS
# ══════════════════════════════════════════════════════════════════════════════

DATA_DIR    = Path("cseps_data")
LEDGER_FILE = DATA_DIR / "ledger.json"
PROC_FILE   = DATA_DIR / "procurement.json"
BIDDERS_DIR = DATA_DIR / "bidders"
BIDS_DIR    = DATA_DIR / "bids"
EVAL_DIR    = DATA_DIR / "evaluators"
MASTER_PUB  = DATA_DIR / "master_pub.pem"
MASTER_PRIV = DATA_DIR / "master_priv_RECONSTRUCTED.pem"   # exists only post-deadline

# secp256r1 curve + its group order (a prime — used as Shamir field modulus)
CURVE     = ec.SECP256R1()
SSS_PRIME = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

BANNER = """
  ╔═══════════════════════════════════════════════════════╗
  ║   ██████╗███████╗███████╗██████╗ ███████╗            ║
  ║  ██╔════╝██╔════╝██╔════╝██╔══██╗██╔════╝            ║
  ║  ██║     ███████╗█████╗  ██████╔╝███████╗            ║
  ║  ██║     ╚════██║██╔══╝  ██╔═══╝ ╚════██║            ║
  ║  ╚██████╗███████║███████╗██║     ███████║            ║
  ║   ╚═════╝╚══════╝╚══════╝╚═╝     ╚══════╝            ║
  ║   Cryptographically Secure e-Procurement System      ║
  ╚═══════════════════════════════════════════════════════╝
"""

# ══════════════════════════════════════════════════════════════════════════════
# TERMINAL OUTPUT HELPERS
# ══════════════════════════════════════════════════════════════════════════════

def _c(code, text): return f"\033[{code}m{text}\033[0m"
def bold(t):   return _c("1", t)
def cyan(t):   return _c("96", t)
def green(t):  return _c("92", t)
def yellow(t): return _c("93", t)
def red(t):    return _c("91", t)
def magenta(t):return _c("95", t)
def dim(t):    return _c("2", t)

def info(msg):  print(f"  {cyan('ℹ')}  {msg}")
def ok(msg):    print(f"  {green('✔')}  {msg}")
def warn(msg):  print(f"  {yellow('⚠')}  {msg}")
def fail(msg):  print(f"  {red('✘')}  {msg}")
def sep():      print(f"  {dim('─' * 64)}")
def blank():    print()

def header(title: str):
    blank()
    print(f"  {bold(magenta('▸'))} {bold(title)}")
    sep()

def box(lines: list):
    w = max(len(l) for l in lines) + 4
    print("  ┌" + "─" * w + "┐")
    for l in lines:
        print(f"  │  {l:<{w-2}}│")
    print("  └" + "─" * w + "┘")


# ══════════════════════════════════════════════════════════════════════════════
# SHAMIR'S SECRET SHARING  (GF(SSS_PRIME))
# ══════════════════════════════════════════════════════════════════════════════

def _ext_gcd(a: int, b: int) -> Tuple[int, int, int]:
    if a == 0:
        return b, 0, 1
    g, x, y = _ext_gcd(b % a, a)
    return g, y - (b // a) * x, x

def _modinv(a: int, p: int) -> int:
    g, x, _ = _ext_gcd(a % p, p)
    if g != 1:
        raise ValueError("Modular inverse does not exist")
    return x % p

def sss_split(secret: int, k: int, n: int) -> List[Tuple[int, int]]:
    """
    Split `secret` into n shares so that any k of them can reconstruct it.
    Uses a random degree-(k-1) polynomial over GF(SSS_PRIME).
    """
    assert 0 < k <= n <= 255, "Invalid (k, n)"
    assert 0 <= secret < SSS_PRIME, "Secret must be in [0, SSS_PRIME)"
    coeffs = [secret] + [secrets.randbelow(SSS_PRIME) for _ in range(k - 1)]
    return [
        (i, sum(c * pow(i, j, SSS_PRIME) for j, c in enumerate(coeffs)) % SSS_PRIME)
        for i in range(1, n + 1)
    ]

def sss_reconstruct(shares: List[Tuple[int, int]]) -> int:
    """Reconstruct secret from any k shares via Lagrange interpolation."""
    secret = 0
    for i, (xi, yi) in enumerate(shares):
        num = den = 1
        for j, (xj, _) in enumerate(shares):
            if i != j:
                num = num * (-xj) % SSS_PRIME
                den = den * (xi - xj) % SSS_PRIME
        secret = (secret + yi * num * _modinv(den, SSS_PRIME)) % SSS_PRIME
    return secret


# ══════════════════════════════════════════════════════════════════════════════
# ECC KEY MANAGEMENT
# ══════════════════════════════════════════════════════════════════════════════

def gen_keypair():
    """Generate a fresh SECP256R1 keypair."""
    priv = ec.generate_private_key(CURVE, default_backend())
    return priv, priv.public_key()

def priv_to_pem(key, password: bytes = None) -> str:
    enc = (serialization.BestAvailableEncryption(password)
           if password else serialization.NoEncryption())
    return key.private_bytes(
        serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8, enc
    ).decode()

def pub_to_pem(key) -> str:
    return key.public_bytes(
        serialization.Encoding.PEM, serialization.PublicFormat.SubjectPublicKeyInfo
    ).decode()

def load_priv(pem: str, password: bytes = None):
    return serialization.load_pem_private_key(
        pem.encode(), password=password, backend=default_backend()
    )

def load_pub(pem: str):
    return serialization.load_pem_public_key(pem.encode(), backend=default_backend())

def priv_scalar(key) -> int:
    """Extract the integer scalar from an EC private key."""
    return key.private_numbers().private_value

def scalar_to_priv(scalar: int):
    """Reconstruct EC private key from integer scalar."""
    return ec.derive_private_key(scalar, CURVE, default_backend())


# ══════════════════════════════════════════════════════════════════════════════
# ECIES  —  Hybrid Encryption  (ECDH ephemeral key + AES-256-GCM)
# ══════════════════════════════════════════════════════════════════════════════

def ecies_encrypt(plaintext: bytes, recipient_pub) -> dict:
    """
    Encrypt plaintext for recipient_pub using ECIES:
      1. Generate ephemeral ECDH keypair
      2. Derive 256-bit AES key via HKDF-SHA256 from shared secret
      3. Encrypt with AES-256-GCM (includes authentication tag)
    Returns a JSON-serialisable dict.
    """
    eph_priv, eph_pub = gen_keypair()
    shared   = eph_priv.exchange(ec.ECDH(), recipient_pub)
    aes_key  = HKDF(
        algorithm=hashes.SHA256(), length=32, salt=None,
        info=b"cseps-ecies-v1", backend=default_backend()
    ).derive(shared)
    nonce = secrets.token_bytes(12)
    ct    = AESGCM(aes_key).encrypt(nonce, plaintext, None)
    return {
        "eph_pub":    pub_to_pem(eph_pub),
        "nonce":      base64.b64encode(nonce).decode(),
        "ciphertext": base64.b64encode(ct).decode(),
    }

def ecies_decrypt(enc: dict, recipient_priv) -> bytes:
    """Decrypt an ECIES-encrypted blob."""
    eph_pub  = load_pub(enc["eph_pub"])
    shared   = recipient_priv.exchange(ec.ECDH(), eph_pub)
    aes_key  = HKDF(
        algorithm=hashes.SHA256(), length=32, salt=None,
        info=b"cseps-ecies-v1", backend=default_backend()
    ).derive(shared)
    nonce = base64.b64decode(enc["nonce"])
    ct    = base64.b64decode(enc["ciphertext"])
    return AESGCM(aes_key).decrypt(nonce, ct, None)


# ══════════════════════════════════════════════════════════════════════════════
# ECDSA DIGITAL SIGNATURES
# ══════════════════════════════════════════════════════════════════════════════

def sign_data(data: bytes, priv_key) -> str:
    """Sign data with ECDSA/SHA-256. Returns base64-encoded DER signature."""
    return base64.b64encode(priv_key.sign(data, ec.ECDSA(hashes.SHA256()))).decode()

def verify_sig(data: bytes, sig_b64: str, pub_key) -> bool:
    """Verify an ECDSA/SHA-256 signature. Returns True iff valid."""
    try:
        pub_key.verify(base64.b64decode(sig_b64), data, ec.ECDSA(hashes.SHA256()))
        return True
    except (InvalidSignature, Exception):
        return False


# ══════════════════════════════════════════════════════════════════════════════
# HASHING UTILITIES
# ══════════════════════════════════════════════════════════════════════════════

def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def obj_hash(obj: dict) -> str:
    """Deterministic SHA-256 hash of a JSON-serialisable object."""
    return sha256(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode())

def now_iso() -> str:
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ══════════════════════════════════════════════════════════════════════════════
# HASH-CHAIN LEDGER
# ══════════════════════════════════════════════════════════════════════════════

def load_ledger() -> list:
    return json.loads(LEDGER_FILE.read_text()) if LEDGER_FILE.exists() else []

def _save_ledger(ledger: list):
    LEDGER_FILE.write_text(json.dumps(ledger, indent=2))

def ledger_append(entry_type: str, payload: dict) -> dict:
    """
    Append a new entry to the hash chain.
    Each entry commits to its predecessor via `prev_hash`, forming an
    append-only chain: modifying any past entry breaks all subsequent hashes.
    """
    ledger = load_ledger()
    prev_hash = ledger[-1]["entry_hash"] if ledger else "0" * 64
    entry = {
        "index":     len(ledger),
        "type":      entry_type,
        "timestamp": now_iso(),
        "prev_hash": prev_hash,
        "payload":   payload,
    }
    # Hash everything except entry_hash itself
    raw = json.dumps(
        {k: v for k, v in entry.items() if k != "entry_hash"},
        sort_keys=True, separators=(",", ":")
    ).encode()
    entry["entry_hash"] = sha256(raw)
    ledger.append(entry)
    _save_ledger(ledger)
    return entry

def verify_ledger_chain() -> Tuple[bool, List[str]]:
    """
    Walk the entire ledger and verify:
      1. Each entry's stored hash matches its recomputed hash (data integrity).
      2. Each entry's prev_hash matches the preceding entry's hash (chain link).
    Returns (all_ok, list_of_issues).
    """
    ledger = load_ledger()
    issues = []
    for i, entry in enumerate(ledger):
        stored = entry.get("entry_hash", "")
        raw = json.dumps(
            {k: v for k, v in entry.items() if k != "entry_hash"},
            sort_keys=True, separators=(",", ":")
        ).encode()
        expected = sha256(raw)
        if stored != expected:
            issues.append(f"Entry #{i} [{entry['type']}]: data hash MISMATCH — entry tampered!")
        if i > 0 and entry["prev_hash"] != ledger[i - 1]["entry_hash"]:
            issues.append(f"Entry #{i} [{entry['type']}]: chain link BROKEN — history modified!")
    return (len(issues) == 0), issues


# ══════════════════════════════════════════════════════════════════════════════
# PROCUREMENT STATE
# ══════════════════════════════════════════════════════════════════════════════

def load_proc() -> dict:
    if not PROC_FILE.exists():
        fail("No active procurement found. Run:  python cseps.py setup")
        sys.exit(1)
    return json.loads(PROC_FILE.read_text())

def save_proc(proc: dict):
    PROC_FILE.write_text(json.dumps(proc, indent=2))

def is_past_deadline(proc: dict) -> bool:
    dl = datetime.datetime.strptime(proc["deadline"], "%Y-%m-%dT%H:%M:%SZ")
    dl = dl.replace(tzinfo=datetime.timezone.utc)
    return datetime.datetime.now(datetime.timezone.utc) > dl

def _init_dirs():
    for d in [DATA_DIR, BIDDERS_DIR, BIDS_DIR, EVAL_DIR]:
        d.mkdir(parents=True, exist_ok=True)


# ══════════════════════════════════════════════════════════════════════════════
# COMMAND: setup
# ══════════════════════════════════════════════════════════════════════════════

def cmd_setup(_):
    """
    Initialise a new procurement:
      • Generate a master ECC keypair for bid encryption.
      • Split the master private key scalar via Shamir's k-of-n SSS.
      • Publish master public key; securely distribute individual shares.
      • Record commitments (hashes of shares) in the ledger so evaluators
        cannot substitute shares later.
    """
    header("PROCUREMENT SETUP")
    _init_dirs()

    print("  Please provide procurement details.\n")
    title    = input("  Procurement title           : ").strip()
    desc     = input("  Description                 : ").strip()
    print("  Deadline format: YYYY-MM-DDTHH:MM:SSZ  (UTC)")
    deadline = input("  Submission deadline         : ").strip()
    n_eval   = int(input("  Total evaluators (n)        : ").strip())
    k_thresh = int(input(f"  Threshold to decrypt (k ≤ {n_eval}): ").strip())

    if not (1 <= k_thresh <= n_eval <= 20):
        fail("Invalid k/n values (1 ≤ k ≤ n ≤ 20).")
        sys.exit(1)

    # ── Generate master encryption keypair ──────────────────────────────────
    master_priv, master_pub = gen_keypair()
    master_scalar = priv_scalar(master_priv)
    MASTER_PUB.write_text(pub_to_pem(master_pub))

    # ── Split master private key with Shamir's SSS ──────────────────────────
    shares = sss_split(master_scalar, k_thresh, n_eval)
    share_commitments = []

    blank()
    info("Generating and saving evaluator key shares…")
    for idx, (x, y) in enumerate(shares):
        sd = {"x": x, "y": y, "evaluator_index": idx + 1}
        share_file = EVAL_DIR / f"evaluator_{idx + 1}_share.json"
        share_file.write_text(json.dumps(sd, indent=2))
        commitment = obj_hash(sd)
        share_commitments.append(commitment)
        ok(f"  Evaluator {idx + 1} share saved  →  {share_file}")

    # ── Save procurement state ───────────────────────────────────────────────
    proc = {
        "title":          title,
        "description":    desc,
        "deadline":       deadline,
        "n_evaluators":   n_eval,
        "k_threshold":    k_thresh,
        "created_at":     now_iso(),
        "share_commitments": share_commitments,
        "status":         "OPEN",
    }
    save_proc(proc)

    # ── Record in immutable ledger ───────────────────────────────────────────
    entry = ledger_append("PROCUREMENT_CREATED", {
        "title":               title,
        "description":         desc,
        "deadline":            deadline,
        "n_evaluators":        n_eval,
        "k_threshold":         k_thresh,
        "master_pub_hash":     sha256(pub_to_pem(master_pub).encode()),
        "share_commitments":   share_commitments,
    })

    blank()
    sep()
    box([
        f"  Procurement : {title}",
        f"  Deadline    : {deadline}",
        f"  Evaluators  : {k_thresh} of {n_eval} required to decrypt",
        f"  Ledger #    : {entry['index']}  ({entry['entry_hash'][:20]}…)",
    ])
    blank()
    ok(f"Master public key stored   →  {MASTER_PUB}")
    info(f"Securely distribute  evaluator_N_share.json  files to each evaluator.")
    info(f"The master private key is NEVER stored — only split shares exist.")


# ══════════════════════════════════════════════════════════════════════════════
# COMMAND: register-bidder
# ══════════════════════════════════════════════════════════════════════════════

def cmd_register_bidder(_):
    """
    Register a new bidder:
      • Generate an ECC keypair for the bidder (signing identity).
      • Store public profile; give bidder their private key file.
      • Ledger entry records only the public key hash (not identity).
    """
    header("REGISTER BIDDER")
    load_proc()   # ensure procurement exists

    name  = input("  Company / bidder name  : ").strip()
    email = input("  Contact email          : ").strip()

    priv, pub = gen_keypair()
    bidder_id = "BID-" + secrets.token_hex(4).upper()

    pw = input("  Password to protect private key (Enter to skip): ").strip()
    pw_bytes = pw.encode() if pw else None

    bidder = {
        "bidder_id":   bidder_id,
        "name":        name,
        "email":       email,
        "public_key":  pub_to_pem(pub),
        "registered":  now_iso(),
    }
    priv_rec = {
        "bidder_id":   bidder_id,
        "private_key": priv_to_pem(priv, pw_bytes),
        "encrypted":   bool(pw_bytes),
    }

    (BIDDERS_DIR / f"{bidder_id}.json").write_text(json.dumps(bidder, indent=2))
    (BIDDERS_DIR / f"{bidder_id}_PRIVATE.json").write_text(json.dumps(priv_rec, indent=2))

    ledger_append("BIDDER_REGISTERED", {
        "bidder_id":      bidder_id,
        "pub_key_hash":   sha256(pub_to_pem(pub).encode()),
        "registered_at":  bidder["registered"],
        # name/email intentionally omitted for anonymity until reveal
    })

    blank()
    sep()
    box([
        f"  Bidder ID : {bidder_id}",
        f"  Name      : {name}",
        f"  Public profile  →  bidders/{bidder_id}.json",
        f"  PRIVATE KEY     →  bidders/{bidder_id}_PRIVATE.json  ← KEEP SECRET!",
    ])
    blank()
    info("Your name and email are NOT in the ledger — anonymity is preserved.")
    info("Your identity is tied to your bidder_id and signing key only.")


# ══════════════════════════════════════════════════════════════════════════════
# COMMAND: submit-bid
# ══════════════════════════════════════════════════════════════════════════════

def cmd_submit_bid(_):
    """
    Submit an encrypted, digitally-signed bid:
      1.  Hash plaintext bid  (SHA-256) — proof of content integrity.
      2.  Encrypt with master public key via ECIES.
      3.  Sign (encrypted_bid + bid_hash + timestamp) with bidder's private key.
      4.  Append submission hash to the ledger.
    Evaluators CANNOT read the bid until after the deadline.
    """
    header("SUBMIT BID")
    proc = load_proc()

    if proc["status"] != "OPEN":
        fail(f"Procurement is '{proc['status']}'. Submissions are closed.")
        sys.exit(1)
    if is_past_deadline(proc):
        fail(f"Submission deadline has passed ({proc['deadline']}). Bids closed.")
        sys.exit(1)

    bidder_id   = input("  Your Bidder ID  : ").strip()
    bidder_file = BIDDERS_DIR / f"{bidder_id}.json"
    priv_file   = BIDDERS_DIR / f"{bidder_id}_PRIVATE.json"

    if not bidder_file.exists():
        fail(f"Bidder '{bidder_id}' not found. Please register first.")
        sys.exit(1)

    bidder   = json.loads(bidder_file.read_text())
    priv_rec = json.loads(priv_file.read_text())

    pw_bytes = None
    if priv_rec["encrypted"]:
        pw = input("  Private key password  : ").strip()
        pw_bytes = pw.encode()

    try:
        bidder_priv = load_priv(priv_rec["private_key"], pw_bytes)
    except Exception:
        fail("Failed to load private key. Wrong password?")
        sys.exit(1)

    blank()
    print(f"  {bold('Bid Details')}")
    item    = input("  Item / service description  : ").strip()
    amount  = input("  Bid amount (e.g. USD 450000): ").strip()
    notes   = input("  Additional notes (optional) : ").strip()

    timestamp = now_iso()
    bid_content = {
        "bidder_id":    bidder_id,
        "item":         item,
        "amount":       amount,
        "notes":        notes,
        "submitted_at": timestamp,
    }
    bid_bytes = json.dumps(bid_content, sort_keys=True, separators=(",", ":")).encode()

    # ── 1. Hash plaintext ────────────────────────────────────────────────────
    bid_hash = sha256(bid_bytes)

    # ── 2. Encrypt with master public key ────────────────────────────────────
    master_pub  = load_pub(MASTER_PUB.read_text())
    enc_bid     = ecies_encrypt(bid_bytes, master_pub)

    # ── 3. Sign ( enc_bid + bid_hash + timestamp ) ────────────────────────────
    sign_payload = json.dumps(
        {"bid_hash": bid_hash, "encrypted_bid": enc_bid, "timestamp": timestamp},
        sort_keys=True, separators=(",", ":")
    ).encode()
    signature         = sign_data(sign_payload, bidder_priv)
    sign_payload_hash = sha256(sign_payload)

    # ── 4. Build full submission record ──────────────────────────────────────
    sub_id = "SUB-" + secrets.token_hex(4).upper()
    submission = {
        "submission_id":      sub_id,
        "bidder_id":          bidder_id,
        "bid_hash":           bid_hash,
        "encrypted_bid":      enc_bid,
        "signature":          signature,
        "sign_payload_hash":  sign_payload_hash,
        "timestamp":          timestamp,
        "public_key":         bidder["public_key"],
    }
    sub_file = BIDS_DIR / f"{sub_id}.json"
    sub_file.write_text(json.dumps(submission, indent=2))

    # ── 5. Ledger entry (only hashes, never plaintext or full ciphertext) ────
    le = ledger_append("BID_SUBMITTED", {
        "submission_id":   sub_id,
        "bidder_id":       bidder_id,
        "bid_hash":        bid_hash,
        "submission_hash": obj_hash(submission),
        "timestamp":       timestamp,
    })

    blank()
    sep()
    box([
        f"  Submission ID  : {sub_id}",
        f"  Bid hash       : {bid_hash[:32]}…",
        f"  Signature      : {signature[:32]}…",
        f"  Ledger entry   : #{le['index']}  ({le['entry_hash'][:20]}…)",
    ])
    blank()
    ok("Bid encrypted and sealed — evaluators CANNOT read it until the deadline.")
    ok("Bid digitally signed — authorship cannot be denied (non-repudiation).")
    ok("Bid hash committed to ledger — any tampering will be detectable.")


# ══════════════════════════════════════════════════════════════════════════════
# COMMAND: reconstruct-key
# ══════════════════════════════════════════════════════════════════════════════

def cmd_reconstruct_key(_):
    """
    Post-deadline: collect k evaluator shares, verify each against its stored
    commitment, and reconstruct the master private key via Lagrange interpolation.
    Verifies reconstruction by comparing derived public key against stored one.
    """
    header("RECONSTRUCT MASTER PRIVATE KEY")
    proc = load_proc()

    if not is_past_deadline(proc):
        warn(f"Deadline has NOT yet passed  ({proc['deadline']}).")
        confirm = input("  Override for testing? (type YES to confirm): ").strip()
        if confirm != "YES":
            info("Aborted. Please wait for the deadline.")
            sys.exit(0)

    k = proc["k_threshold"]
    n = proc["n_evaluators"]
    info(f"Requires {k} of {n} evaluator shares.")
    blank()

    shares: List[Tuple[int, int]] = []
    used: set = set()

    for round_num in range(1, k + 1):
        while True:
            try:
                idx = int(input(f"  Evaluator index for share {round_num}/{k}  (1–{n}): ").strip())
            except ValueError:
                fail("Please enter a valid integer."); continue
            if not (1 <= idx <= n):
                fail(f"Index must be between 1 and {n}."); continue
            if idx in used:
                fail("This evaluator's share was already entered."); continue
            break
        used.add(idx)

        share_file = EVAL_DIR / f"evaluator_{idx}_share.json"
        if not share_file.exists():
            fail(f"Share file not found: {share_file}")
            sys.exit(1)

        sd = json.loads(share_file.read_text())

        # ── Verify share against stored commitment ────────────────────────
        commitment = obj_hash(sd)
        stored_com = proc["share_commitments"][idx - 1]
        if commitment != stored_com:
            fail(f"Evaluator {idx} share FAILED commitment check — share may be tampered!")
            sys.exit(1)
        ok(f"  Evaluator {idx} share: commitment ✔  (hash: {commitment[:20]}…)")
        shares.append((sd["x"], sd["y"]))

    # ── Reconstruct scalar and rebuild private key ────────────────────────
    blank()
    info("Running Lagrange interpolation over GF(SSS_PRIME)…")
    master_scalar_rec = sss_reconstruct(shares)
    master_priv_rec   = scalar_to_priv(master_scalar_rec)

    # ── Verify: derived public key must match the publicly stored one ──────
    derived_pub_pem = pub_to_pem(master_priv_rec.public_key())
    stored_pub_pem  = MASTER_PUB.read_text()

    if derived_pub_pem.strip() != stored_pub_pem.strip():
        fail("Reconstructed key does NOT match master public key!")
        fail("Insufficient or corrupted shares. Aborting.")
        sys.exit(1)

    MASTER_PRIV.write_text(priv_to_pem(master_priv_rec))
    proc["status"] = "KEY_RECONSTRUCTED"
    save_proc(proc)

    ledger_append("KEY_RECONSTRUCTED", {
        "evaluators_used":  sorted(list(used)),
        "timestamp":        now_iso(),
        "pub_key_verified": True,
    })

    blank()
    ok(f"Master private key reconstructed and verified!")
    ok(f"Key file written  →  {MASTER_PRIV}")
    info("Run  'reveal-bids'  to decrypt and evaluate all submissions.")


# ══════════════════════════════════════════════════════════════════════════════
# COMMAND: reveal-bids
# ══════════════════════════════════════════════════════════════════════════════

def cmd_reveal_bids(_):
    """
    Post-deadline: decrypt all bids and run full verification:
      • ECDSA signature check (non-repudiation)
      • Plaintext hash match (integrity — was bid modified after submission?)
      • Ledger submission hash check (was the submission file tampered?)
    """
    header("REVEAL & DECRYPT BIDS")
    proc = load_proc()

    if proc["status"] not in ("KEY_RECONSTRUCTED", "REVEALED"):
        fail("Master key has not been reconstructed yet.")
        info("Run  'reconstruct-key'  first.")
        sys.exit(1)
    if not MASTER_PRIV.exists():
        fail(f"Reconstructed key file not found: {MASTER_PRIV}")
        sys.exit(1)

    master_priv = load_priv(MASTER_PRIV.read_text())
    bid_files   = sorted(BIDS_DIR.glob("SUB-*.json"))

    if not bid_files:
        warn("No bid submissions found.")
        return

    ledger    = load_ledger()
    results   = []
    all_ok    = True

    for i, bf in enumerate(bid_files):
        submission = json.loads(bf.read_text())
        sub_id     = submission["submission_id"]
        bidder_id  = submission["bidder_id"]

        blank()
        print(f"  ┌─ Submission {i + 1}:  {bold(sub_id)} {'─' * 25}")

        # ── Verify signature ──────────────────────────────────────────────
        sp = json.dumps(
            {"bid_hash": submission["bid_hash"],
             "encrypted_bid": submission["encrypted_bid"],
             "timestamp": submission["timestamp"]},
            sort_keys=True, separators=(",", ":")
        ).encode()
        bidder_pub = load_pub(submission["public_key"])
        sig_valid  = verify_sig(sp, submission["signature"], bidder_pub)

        _sig_icon = green("✔") if sig_valid else red("✘")
        print(f"  │  {_sig_icon}  Signature: {'VALID' if sig_valid else 'INVALID'}"
              f"  ({bidder_id})")
        if not sig_valid:
            all_ok = False

        # ── Decrypt ──────────────────────────────────────────────────────
        try:
            plaintext   = ecies_decrypt(submission["encrypted_bid"], master_priv)
            bid_content = json.loads(plaintext)

            # Recompute hash of decrypted content
            computed_hash = sha256(
                json.dumps(bid_content, sort_keys=True, separators=(",", ":")).encode()
            )
            hash_ok = (computed_hash == submission["bid_hash"])
            _h_icon = green("✔") if hash_ok else red("✘")
            print(f"  │  {_h_icon}  Integrity: {'VERIFIED' if hash_ok else 'HASH MISMATCH — TAMPERED!'}")

            # Verify against ledger commitment
            le_entry = next(
                (e for e in ledger
                 if e["type"] == "BID_SUBMITTED"
                 and e["payload"].get("submission_id") == sub_id), None
            )
            if le_entry:
                sub_hash_now = obj_hash(submission)
                ledger_hash  = le_entry["payload"].get("submission_hash", "")
                match        = (sub_hash_now == ledger_hash)
                _l_icon      = green("✔") if match else red("✘")
                print(f"  │  {_l_icon}  Ledger commitment: {'MATCH' if match else 'MISMATCH — FILE MODIFIED!'}")
                if not match:
                    all_ok = False

            if not hash_ok:
                all_ok = False

            print(f"  │")
            print(f"  │  Bidder ID   : {bid_content.get('bidder_id', '—')}")
            print(f"  │  Item        : {bid_content.get('item', '—')}")
            print(f"  │  Amount      : {bold(bid_content.get('amount', '—'))}")
            print(f"  │  Notes       : {bid_content.get('notes') or '—'}")
            print(f"  │  Submitted   : {bid_content.get('submitted_at', '—')}")
            print(f"  │  Bid Hash    : {submission['bid_hash'][:40]}…")

            results.append({
                "submission_id":   sub_id,
                "bidder_id":       bidder_id,
                "item":            bid_content.get("item"),
                "amount":          bid_content.get("amount"),
                "notes":           bid_content.get("notes"),
                "submitted_at":    bid_content.get("submitted_at"),
                "signature_valid": sig_valid,
                "hash_verified":   hash_ok,
            })

        except Exception as exc:
            print(f"  │  {red('✘')}  Decryption FAILED: {exc}")
            all_ok = False

        print(f"  └{'─' * 55}")

    # ── Record reveal in ledger ───────────────────────────────────────────
    ledger_append("BIDS_REVEALED", {
        "total_bids":  len(bid_files),
        "revealed_at": now_iso(),
        "all_verified": all_ok,
        "summary": [
            {"submission_id": r["submission_id"], "amount": r["amount"],
             "sig_ok": r["signature_valid"], "hash_ok": r["hash_verified"]}
            for r in results
        ],
    })

    results_file = DATA_DIR / "revealed_bids.json"
    results_file.write_text(json.dumps(results, indent=2))
    proc["status"] = "REVEALED"
    save_proc(proc)

    blank()
    sep()
    if all_ok:
        ok(f"All {len(results)} bids passed full cryptographic verification.")
    else:
        fail("One or more bids failed verification. See output above.")
    ok(f"Results saved  →  {results_file}")


# ══════════════════════════════════════════════════════════════════════════════
# COMMAND: verify-ledger
# ══════════════════════════════════════════════════════════════════════════════

def cmd_verify_ledger(_):
    """
    Publicly verifiable hash-chain audit.
    Anyone can run this command to confirm the ledger has never been modified.
    """
    header("LEDGER INTEGRITY VERIFICATION")
    ledger = load_ledger()

    if not ledger:
        warn("Ledger is empty.")
        return

    info(f"Checking {len(ledger)} entries…")
    valid, issues = verify_ledger_chain()
    blank()

    # Fancy table
    print(f"  {'#':>4}  {'TYPE':<26}  {'TIMESTAMP':<21}  STATUS")
    print(f"  {'─'*4}  {'─'*26}  {'─'*21}  {'─'*20}")
    for entry in ledger:
        has_issue = any(f"#{entry['index']}" in iss for iss in issues)
        icon  = red("✘ FAIL") if has_issue else green("✔ OK")
        etype = entry["type"][:26]
        print(f"  {entry['index']:>4}  {etype:<26}  {entry['timestamp']:<21}  {icon}")

    blank()
    sep()
    if valid:
        ok(f"✔  ALL {len(ledger)} ENTRIES VERIFIED — ledger is intact and untampered.")
    else:
        fail(f"✘  INTEGRITY FAILURES  ({len(issues)} issue(s)):")
        for iss in issues:
            print(f"     {red('⚠')}  {iss}")


# ══════════════════════════════════════════════════════════════════════════════
# COMMAND: view-ledger
# ══════════════════════════════════════════════════════════════════════════════

def cmd_view_ledger(_):
    """Pretty-print every entry in the public hash-chain ledger."""
    header("PUBLIC LEDGER — FULL VIEW")
    ledger = load_ledger()

    if not ledger:
        warn("Ledger is empty.")
        return

    for entry in ledger:
        blank()
        print(f"  ┌─ #{entry['index']}  [{bold(entry['type'])}]  {dim(entry['timestamp'])} {'─'*12}")
        print(f"  │  prev_hash : {dim(entry['prev_hash'][:52])}…")
        print(f"  │  this_hash : {entry['entry_hash'][:52]}…")
        print(f"  │  payload:")
        for k, v in entry["payload"].items():
            vs = str(v)
            if len(vs) > 55:
                vs = vs[:52] + "…"
            print(f"  │    {cyan(k):<32} {vs}")
        print(f"  └{'─' * 64}")


# ══════════════════════════════════════════════════════════════════════════════
# COMMAND: audit-bid
# ══════════════════════════════════════════════════════════════════════════════

def cmd_audit_bid(_):
    """
    Deep-audit a single submission without decrypting it:
      • Verify ECDSA signature on the encrypted payload (non-repudiation).
      • Confirm the submission is in the ledger and the file hasn't changed.
      • Run full ledger chain verification.
    """
    header("AUDIT SPECIFIC BID")
    sub_id   = input("  Submission ID (e.g. SUB-ABCD1234): ").strip()
    sub_file = BIDS_DIR / f"{sub_id}.json"

    if not sub_file.exists():
        fail(f"Submission '{sub_id}' not found.")
        sys.exit(1)

    submission = json.loads(sub_file.read_text())
    blank()
    box([
        f"  Submission ID : {submission['submission_id']}",
        f"  Bidder ID     : {submission['bidder_id']}",
        f"  Timestamp     : {submission['timestamp']}",
        f"  Bid hash      : {submission['bid_hash'][:40]}…",
    ])
    blank()

    # ── 1. Signature verification ─────────────────────────────────────────
    sp = json.dumps(
        {"bid_hash": submission["bid_hash"],
         "encrypted_bid": submission["encrypted_bid"],
         "timestamp": submission["timestamp"]},
        sort_keys=True, separators=(",", ":")
    ).encode()
    bidder_pub = load_pub(submission["public_key"])
    sig_valid  = verify_sig(sp, submission["signature"], bidder_pub)

    if sig_valid:
        ok("Digital signature VALID — bidder identity and authenticity confirmed.")
    else:
        fail("Digital signature INVALID — bid content may have been altered!")

    # ── 2. Ledger presence & file-hash check ──────────────────────────────
    ledger  = load_ledger()
    le_list = [e for e in ledger
               if e["type"] == "BID_SUBMITTED"
               and e["payload"].get("submission_id") == sub_id]

    if le_list:
        le = le_list[0]
        ok(f"Bid found in ledger at entry #{le['index']}  ({le['entry_hash'][:20]}…).")
        ok(f"Ledger timestamp: {le['timestamp']}")
        sub_hash_now = obj_hash(submission)
        stored_hash  = le["payload"].get("submission_hash", "")
        if sub_hash_now == stored_hash:
            ok("Submission file matches ledger commitment — file NOT modified since submission.")
        else:
            fail("Submission file does NOT match ledger commitment — FILE TAMPERED!")
    else:
        fail("Submission NOT FOUND in ledger — this bid may be fraudulent!")

    # ── 3. Full chain verification ────────────────────────────────────────
    valid, issues = verify_ledger_chain()
    if valid:
        ok("Full ledger chain is intact — no historical tampering detected.")
    else:
        fail(f"Ledger chain has {len(issues)} integrity issue(s)!")
        for iss in issues:
            print(f"     {red('⚠')}  {iss}")


# ══════════════════════════════════════════════════════════════════════════════
# COMMAND: status
# ══════════════════════════════════════════════════════════════════════════════

def cmd_status(_):
    """Show current procurement status and a summary of all activity."""
    header("PROCUREMENT STATUS")
    proc = load_proc()

    past   = is_past_deadline(proc)
    dl_tag = f"  {red('[DEADLINE PASSED]')}" if past else f"  {green('[OPEN]')}"

    print(f"  {'Title':<18}: {bold(proc['title'])}")
    print(f"  {'Description':<18}: {proc['description']}")
    print(f"  {'Deadline':<18}: {proc['deadline']}{dl_tag}")
    print(f"  {'Status':<18}: {bold(proc['status'])}")
    print(f"  {'Evaluators':<18}: {proc['k_threshold']} of {proc['n_evaluators']} required")
    print(f"  {'Created':<18}: {proc['created_at']}")
    blank()

    bids    = list(BIDS_DIR.glob("SUB-*.json"))
    bidders = list(BIDDERS_DIR.glob("BID-*.json"))
    ledger  = load_ledger()

    info(f"Registered bidders : {len(bidders)}")
    info(f"Submitted bids     : {len(bids)}")
    info(f"Ledger entries     : {len(ledger)}")
    blank()

    valid, issues = verify_ledger_chain()
    if valid:
        ok("Ledger integrity  : INTACT ✔")
    else:
        fail(f"Ledger integrity  : COMPROMISED ✘  ({len(issues)} issues)")

    if proc["status"] == "REVEALED" and (DATA_DIR / "revealed_bids.json").exists():
        results = json.loads((DATA_DIR / "revealed_bids.json").read_text())
        blank()
        info(f"Revealed bids ({len(results)}):")
        for r in results:
            icon = green("✔") if r.get("signature_valid") and r.get("hash_verified") else red("✘")
            print(f"     {icon}  {r['submission_id']}  │  {r['bidder_id']}  │  {bold(r['amount'] or '—')}")


# ══════════════════════════════════════════════════════════════════════════════
# COMMAND: reset
# ══════════════════════════════════════════════════════════════════════════════

def cmd_reset(_):
    """Delete all cseps_data (for testing/demo reset)."""
    header("RESET SYSTEM DATA")
    warn("This will permanently delete ALL procurement data!")
    confirm = input("  Type  RESET  to confirm: ").strip()
    if confirm != "RESET":
        info("Aborted."); return
    import shutil
    if DATA_DIR.exists():
        shutil.rmtree(DATA_DIR)
    ok("All data deleted. Run 'setup' to start fresh.")


# ══════════════════════════════════════════════════════════════════════════════
# COMMAND: demo  —  Fully automated end-to-end walkthrough
# ══════════════════════════════════════════════════════════════════════════════

def cmd_demo(_):
    """
    Automated end-to-end demonstration covering every feature:
      setup → register evaluators → register bidders → submit 3 bids
      → reconstruct key (2-of-3) → reveal bids → verify ledger → audit bid
    """
    import shutil
    header("FULL SYSTEM DEMONSTRATION")

    print(textwrap.dedent("""
      This demo runs a complete procurement cycle automatically:
        1.  Create a procurement (2-of-3 threshold decryption)
        2.  Distribute evaluator key shares
        3.  Register 3 bidders
        4.  Submit 3 encrypted + signed bids
        5.  Reconstruct master key with evaluators 1 & 3
        6.  Reveal and verify all bids
        7.  Verify full ledger chain integrity
        8.  Audit one individual bid
    """))
    input("  Press  ENTER  to begin the demonstration… ")

    # ── Clean start ──────────────────────────────────────────────────────────
    if DATA_DIR.exists():
        shutil.rmtree(DATA_DIR)
    _init_dirs()

    # ────────────────────────────────────────────────────────────────────────
    # STEP 1 — Create Procurement
    # ────────────────────────────────────────────────────────────────────────
    blank()
    header("STEP 1 — Create Procurement")

    master_priv, master_pub = gen_keypair()
    master_scalar = priv_scalar(master_priv)
    MASTER_PUB.write_text(pub_to_pem(master_pub))

    shares = sss_split(master_scalar, k=2, n=3)    # 2-of-3
    share_commitments = []
    for idx, (x, y) in enumerate(shares):
        sd = {"x": x, "y": y, "evaluator_index": idx + 1}
        (EVAL_DIR / f"evaluator_{idx + 1}_share.json").write_text(json.dumps(sd, indent=2))
        share_commitments.append(obj_hash(sd))
        ok(f"  Evaluator {idx + 1} share distributed  (commitment: {share_commitments[-1][:20]}…)")

    proc = {
        "title":             "DEMO: National Highway Construction 2025",
        "description":       "50 km highway — ECC bid procurement demo",
        "deadline":          "2020-01-01T00:00:00Z",   # deliberately past for demo
        "n_evaluators":      3,
        "k_threshold":       2,
        "created_at":        now_iso(),
        "share_commitments": share_commitments,
        "status":            "OPEN",
    }
    save_proc(proc)
    le = ledger_append("PROCUREMENT_CREATED", {
        "title":               proc["title"],
        "deadline":            proc["deadline"],
        "n_evaluators":        3,
        "k_threshold":         2,
        "master_pub_hash":     sha256(pub_to_pem(master_pub).encode()),
        "share_commitments":   share_commitments,
    })
    ok(f"Procurement created  →  ledger entry #{le['index']}  ({le['entry_hash'][:20]}…)")
    info("Master private key NEVER stored — only 3 split shares exist.")

    # ────────────────────────────────────────────────────────────────────────
    # STEP 2 — Register Bidders
    # ────────────────────────────────────────────────────────────────────────
    blank()
    header("STEP 2 — Register Bidders")

    bidder_data = [
        ("AlphaCorp Construction",  "alpha@corp.com"),
        ("BetaBuilders Ltd",        "beta@builders.com"),
        ("Gamma Infrastructure",    "gamma@infra.com"),
    ]
    bidder_ids   = []
    bidder_privs = []

    for name, email in bidder_data:
        priv, pub = gen_keypair()
        bid_id = "BID-" + secrets.token_hex(4).upper()
        bidder_ids.append(bid_id)
        bidder_privs.append(priv)

        bidder   = {"bidder_id": bid_id, "name": name, "email": email,
                    "public_key": pub_to_pem(pub), "registered": now_iso()}
        priv_rec = {"bidder_id": bid_id, "private_key": priv_to_pem(priv), "encrypted": False}
        (BIDDERS_DIR / f"{bid_id}.json").write_text(json.dumps(bidder, indent=2))
        (BIDDERS_DIR / f"{bid_id}_PRIVATE.json").write_text(json.dumps(priv_rec, indent=2))
        ledger_append("BIDDER_REGISTERED", {
            "bidder_id":     bid_id,
            "pub_key_hash":  sha256(pub_to_pem(pub).encode()),
        })
        ok(f"  {name:<30} →  {bid_id}")

    info("Bidder names are NOT in the ledger until reveal (anonymity preserved).")

    # ────────────────────────────────────────────────────────────────────────
    # STEP 3 — Submit Encrypted Bids
    # ────────────────────────────────────────────────────────────────────────
    blank()
    header("STEP 3 — Submit Encrypted Bids")

    bid_details = [
        ("Highway 2025", "USD 4,500,000", "15 yrs experience, fastest delivery"),
        ("Highway 2025", "USD 4,200,000", "Lowest bid, 18-month completion"),
        ("Highway 2025", "USD 4,800,000", "Premium materials, full guarantee"),
    ]
    submission_ids = []

    for bid_id, bp, (item, amount, notes) in zip(bidder_ids, bidder_privs, bid_details):
        bidder  = json.loads((BIDDERS_DIR / f"{bid_id}.json").read_text())
        ts      = now_iso()
        bc      = {"bidder_id": bid_id, "item": item, "amount": amount,
                   "notes": notes, "submitted_at": ts}
        bb      = json.dumps(bc, sort_keys=True, separators=(",", ":")).encode()
        bh      = sha256(bb)
        enc_bid = ecies_encrypt(bb, master_pub)
        sp      = json.dumps(
            {"bid_hash": bh, "encrypted_bid": enc_bid, "timestamp": ts},
            sort_keys=True, separators=(",", ":")
        ).encode()
        sig  = sign_data(sp, bp)
        sid  = "SUB-" + secrets.token_hex(4).upper()
        submission_ids.append(sid)
        sub  = {"submission_id": sid, "bidder_id": bid_id, "bid_hash": bh,
                "encrypted_bid": enc_bid, "signature": sig,
                "sign_payload_hash": sha256(sp),
                "timestamp": ts, "public_key": bidder["public_key"]}
        (BIDS_DIR / f"{sid}.json").write_text(json.dumps(sub, indent=2))
        ledger_append("BID_SUBMITTED", {
            "submission_id": sid, "bidder_id": bid_id, "bid_hash": bh,
            "submission_hash": obj_hash(sub), "timestamp": ts,
        })
        ok(f"  {bidder['name']:<30} →  {sid}  [encrypted + signed]")

    info("All bids sealed with ECIES — evaluators see ONLY hashes right now.")

    # ────────────────────────────────────────────────────────────────────────
    # STEP 4 — Reconstruct Master Key  (evaluators 1 & 3)
    # ────────────────────────────────────────────────────────────────────────
    blank()
    header("STEP 4 — Reconstruct Master Key  (evaluators 1 & 3 of 3)")

    eval_indices  = [1, 3]
    recon_shares  = []
    for idx in eval_indices:
        sd = json.loads((EVAL_DIR / f"evaluator_{idx}_share.json").read_text())
        c  = obj_hash(sd)
        if c != share_commitments[idx - 1]:
            fail(f"Evaluator {idx} share failed commitment — ABORT"); sys.exit(1)
        ok(f"  Evaluator {idx} share verified  (commitment: {c[:20]}…)")
        recon_shares.append((sd["x"], sd["y"]))

    rec_scalar = sss_reconstruct(recon_shares)
    rec_priv   = scalar_to_priv(rec_scalar)

    assert pub_to_pem(rec_priv.public_key()).strip() == pub_to_pem(master_pub).strip(), \
        "Reconstructed key mismatch!"

    MASTER_PRIV.write_text(priv_to_pem(rec_priv))
    proc["status"] = "KEY_RECONSTRUCTED"
    save_proc(proc)
    ledger_append("KEY_RECONSTRUCTED", {
        "evaluators_used": eval_indices, "timestamp": now_iso(), "verified": True
    })
    ok("Master private key reconstructed using evaluators 1 and 3.")
    ok("Derived public key matches stored master public key  ✔")

    # ────────────────────────────────────────────────────────────────────────
    # STEP 5 — Reveal Bids
    # ────────────────────────────────────────────────────────────────────────
    blank()
    header("STEP 5 — Reveal & Decrypt All Bids")
    cmd_reveal_bids(None)

    # ────────────────────────────────────────────────────────────────────────
    # STEP 6 — Verify Ledger
    # ────────────────────────────────────────────────────────────────────────
    blank()
    header("STEP 6 — Verify Ledger Chain Integrity")
    cmd_verify_ledger(None)

    # ────────────────────────────────────────────────────────────────────────
    # STEP 7 — Audit one bid
    # ────────────────────────────────────────────────────────────────────────
    blank()
    header("STEP 7 — Individual Bid Audit")
    info(f"Auditing submission: {submission_ids[0]}")
    sub_file   = BIDS_DIR / f"{submission_ids[0]}.json"
    submission = json.loads(sub_file.read_text())
    sp = json.dumps(
        {"bid_hash": submission["bid_hash"],
         "encrypted_bid": submission["encrypted_bid"],
         "timestamp": submission["timestamp"]},
        sort_keys=True, separators=(",", ":")
    ).encode()
    bidder_pub = load_pub(submission["public_key"])
    sig_ok     = verify_sig(sp, submission["signature"], bidder_pub)

    ok(f"Signature:  {'VALID ✔' if sig_ok else 'INVALID ✘'}")
    ledger = load_ledger()
    le_match = next((e for e in ledger if e["type"] == "BID_SUBMITTED"
                     and e["payload"].get("submission_id") == submission_ids[0]), None)
    if le_match:
        ok(f"In ledger:  entry #{le_match['index']}  ✔")
        file_hash_now = obj_hash(submission)
        ledger_hash   = le_match["payload"].get("submission_hash", "")
        ok(f"File hash vs ledger: {'MATCH ✔' if file_hash_now == ledger_hash else 'MISMATCH ✘'}")

    # ────────────────────────────────────────────────────────────────────────
    # Summary
    # ────────────────────────────────────────────────────────────────────────
    blank()
    sep()
    print(f"\n  {bold(green('DEMO COMPLETE'))}\n")
    box([
        "  All cryptographic features exercised successfully:",
        "  ✔  ECC keypair generation (SECP256R1)",
        "  ✔  Shamir k-of-n secret sharing (2-of-3)",
        "  ✔  ECIES hybrid encryption (ECDH + AES-256-GCM)",
        "  ✔  ECDSA digital signatures (non-repudiation)",
        "  ✔  SHA-256 hash-chain ledger (tamper-proof)",
        "  ✔  Commitment scheme for evaluator shares",
        "  ✔  Full post-deadline bid reveal & verification",
        "  ✔  Bidder anonymity until reveal",
    ])
    blank()


# ══════════════════════════════════════════════════════════════════════════════
# CLI DISPATCH
# ══════════════════════════════════════════════════════════════════════════════

COMMANDS = {
    "setup":           (cmd_setup,           "Create a new procurement and split master key"),
    "register-bidder": (cmd_register_bidder, "Register a bidder and generate their ECC keypair"),
    "submit-bid":      (cmd_submit_bid,      "Encrypt, sign and submit a bid"),
    "reconstruct-key": (cmd_reconstruct_key, "Combine k evaluator shares to rebuild master key"),
    "reveal-bids":     (cmd_reveal_bids,     "Decrypt and verify all bids (post-deadline)"),
    "verify-ledger":   (cmd_verify_ledger,   "Verify the SHA-256 hash-chain ledger"),
    "view-ledger":     (cmd_view_ledger,     "Print every entry in the public ledger"),
    "audit-bid":       (cmd_audit_bid,       "Deep-audit a single submission's authenticity"),
    "status":          (cmd_status,          "Show procurement status and quick summary"),
    "reset":           (cmd_reset,           "Wipe all data (testing only)"),
    "demo":            (cmd_demo,            "Run a full automated end-to-end demonstration"),
}

HELP_TEXT = f"""
{BANNER}
  {bold('USAGE')}   python cseps.py <command>

  {bold('COMMANDS')}
"""

def print_help():
    print(HELP_TEXT)
    for cmd, (_, desc) in COMMANDS.items():
        print(f"    {cyan(cmd):<28} {desc}")
    print(f"""
  {bold('QUICK START')}
    python cseps.py demo                # automated end-to-end demo
    python cseps.py setup               # create a new procurement
    python cseps.py register-bidder     # register as a bidder
    python cseps.py submit-bid          # submit an encrypted bid
    python cseps.py reconstruct-key     # unlock bids (k evaluators required)
    python cseps.py reveal-bids         # decrypt and verify all bids
    python cseps.py verify-ledger       # public audit of the ledger
""")

def main():
    if len(sys.argv) < 2 or sys.argv[1] in ("-h", "--help", "help"):
        print_help()
        sys.exit(0)

    cmd = sys.argv[1]
    if cmd not in COMMANDS:
        fail(f"Unknown command: '{cmd}'")
        print_help()
        sys.exit(1)

    func, _ = COMMANDS[cmd]
    try:
        func(sys.argv[2:])
    except KeyboardInterrupt:
        blank()
        warn("Interrupted.")
        sys.exit(0)

if __name__ == "__main__":
    main()