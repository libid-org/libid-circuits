// X token-only circuit (dual blinder)
//
// Two TLSN sessions (/token + /me) each commit the bearer with their OWN
// blinder. The circuit binds them by proving that the same private bearer
// (and the same length) hashes to BOTH attestation commitments, plus a
// blinder-independent nullifier.

use keccak256::keccak256;
use sha256::sha256_var;

/// Blinder size used by tlsn ProxyMode hash commits. The blinder is the
/// notary-secret-shared 16-byte value appended to the plaintext range
/// before SHA-256.
global BLINDER_LEN: u32 = 16;

/// Bearer hard cap. The nullifier preimage pads the bearer to this length
/// so the on-chain hash domain is fixed regardless of the actual bearer
/// length.
global MAX_BEARER_LEN: u32 = 128;

/// Nullifier preimage: bearer padded to `MAX_BEARER_LEN` + 4-byte big-endian
/// length.
global NULLIFIER_INPUT_LEN: u32 = 132;

global BEARER_HASH_INPUT_LEN: u32 = 144; // MAX_BEARER_LEN (128) + BLINDER_LEN (16)

global MIN_BEARER_LEN: u32 = 22;
global MAX_REASONABLE_BEARER_LEN: u32 = 128;

/// Verify a tlsn-style SHA-256 hash commitment: assert that
/// `SHA256(plaintext_padded[0..plaintext_len] || blinder) == expected_hash`.
///
/// Generic over `MAX_PLAIN` (caller's hard cap on plaintext length) and
/// `TOTAL` (caller's `MAX_PLAIN + BLINDER_LEN`, supplied because Noir array
/// types currently can't express `[u8; MAX_PLAIN + BLINDER_LEN]` directly).
/// The first assertion catches a wrong `TOTAL` at proof-gen time.
fn verify_hash_commit<let MAX_PLAIN: u32, let TOTAL: u32>(
    plaintext_padded: [u8; MAX_PLAIN],
    plaintext_len: u32,
    blinder: [u8; BLINDER_LEN],
    expected_hash: [u8; 32],
) {
    assert(TOTAL == MAX_PLAIN + BLINDER_LEN, "TOTAL must equal MAX_PLAIN + BLINDER_LEN");

    let mut input: [u8; TOTAL] = [0; TOTAL];
    for i in 0..MAX_PLAIN {
        if i < plaintext_len {
            input[i] = plaintext_padded[i];
        }
    }
    for i in 0..BLINDER_LEN {
        input[plaintext_len + i] = blinder[i];
    }
    let computed = sha256_var(input, plaintext_len + BLINDER_LEN);
    assert(computed == expected_hash, "hash commit mismatch");
}

/// Derive the session-independent bearer nullifier. Preimage:
/// `bearer_padded || bearer_len.be_bytes(4)`. Deterministic on the
/// (bearer, len) pair so the on-chain dedup is one-shot per real OAuth
/// bearer (combined with the H1 CRLF anchor that canonicalises len).
fn compute_bearer_nullifier(bearer_padded: [u8; MAX_BEARER_LEN], bearer_len: u32) -> [u8; 32] {
    let mut nul_in: [u8; NULLIFIER_INPUT_LEN] = [0; NULLIFIER_INPUT_LEN];
    for i in 0..MAX_BEARER_LEN {
        nul_in[i] = bearer_padded[i];
    }
    nul_in[MAX_BEARER_LEN] = ((bearer_len >> 24) & 0xff) as u8;
    nul_in[MAX_BEARER_LEN + 1] = ((bearer_len >> 16) & 0xff) as u8;
    nul_in[MAX_BEARER_LEN + 2] = ((bearer_len >> 8) & 0xff) as u8;
    nul_in[MAX_BEARER_LEN + 3] = (bearer_len & 0xff) as u8;
    keccak256(nul_in, NULLIFIER_INPUT_LEN)
}

fn main(
    // --- Private ---
    bearer: [u8; MAX_BEARER_LEN],
    bearer_len: u32,
    blinder_token: [u8; BLINDER_LEN],
    blinder_me: [u8; BLINDER_LEN],
    // --- Public ---
    bearer_hash_token: pub [u8; 32], // SHA256(bearer || blinder_token)
    bearer_hash_me: pub [u8; 32], // SHA256(bearer || blinder_me)
    nullifier: pub [u8; 32], // keccak256(bearer_padded || len.be32)
    wallet_address: pub [u8; 20],
    session_addr: pub [u8; 20],
) {
    // Dual commit binding: same private bearer hashes to BOTH notary
    // commitments. Cross-binds /token and /me on chain without requiring
    // the two TLSN sessions to share a blinder.
    verify_hash_commit::<MAX_BEARER_LEN, BEARER_HASH_INPUT_LEN>(
        bearer,
        bearer_len,
        blinder_token,
        bearer_hash_token,
    );
    verify_hash_commit::<MAX_BEARER_LEN, BEARER_HASH_INPUT_LEN>(
        bearer,
        bearer_len,
        blinder_me,
        bearer_hash_me,
    );

    // Blinder-independent nullifier (deterministic across attempts).
    let computed_nullifier = compute_bearer_nullifier(bearer, bearer_len);
    for i in 0..32 {
        assert(computed_nullifier[i] == nullifier[i], "nullifier mismatch");
    }

    // Sanity bounds + zero-pad enforcement.
    assert(bearer_len >= MIN_BEARER_LEN, "bearer too short");
    assert(bearer_len <= MAX_REASONABLE_BEARER_LEN, "bearer too long");
    for i in 0..MAX_BEARER_LEN {
        let b = bearer[i];
        let in_range = (i as u32) < bearer_len;
        assert(in_range | (b == 0), "bearer tail must be zero-padded");
    }

    // wallet_address / session_addr: pub-only, F-S bound, not constrained
    // inside the circuit.
    let _ = wallet_address;
    let _ = session_addr;
}

// --- Tests ----------------------------------------------------------------

#[test]
fn test_nullifier_deterministic() {
    let mut bearer: [u8; MAX_BEARER_LEN] = [0; MAX_BEARER_LEN];
    bearer[0] = 0x61;
    bearer[1] = 0x62;
    bearer[2] = 0x63;
    let n1 = compute_bearer_nullifier(bearer, 3);
    let n2 = compute_bearer_nullifier(bearer, 3);
    for i in 0..32 {
        assert(n1[i] == n2[i], "nullifier non-deterministic");
    }
}

#[test]
fn test_nullifier_length_separates() {
    // Same padded bearer but different `bearer_len` MUST yield different
    // nullifiers -- otherwise an attacker could claim a shorter bearer to
    // collide nullifiers with a longer one ending in zero bytes.
    let mut bearer: [u8; MAX_BEARER_LEN] = [0; MAX_BEARER_LEN];
    bearer[0] = 0x61;
    bearer[1] = 0x62;
    bearer[2] = 0x63;
    let n3 = compute_bearer_nullifier(bearer, 3);
    let n4 = compute_bearer_nullifier(bearer, 4);
    let mut differs = false;
    for i in 0..32 {
        if n3[i] != n4[i] {
            differs = true;
        }
    }
    assert(differs, "nullifier did not separate on bearer_len");
}

#[test]
fn test_nullifier_separates_distinct_bearers() {
    let mut a: [u8; MAX_BEARER_LEN] = [0; MAX_BEARER_LEN];
    a[0] = 0x61;
    let mut b: [u8; MAX_BEARER_LEN] = [0; MAX_BEARER_LEN];
    b[0] = 0x62;
    let na = compute_bearer_nullifier(a, 1);
    let nb = compute_bearer_nullifier(b, 1);
    let mut differs = false;
    for i in 0..32 {
        if na[i] != nb[i] {
            differs = true;
        }
    }
    assert(differs, "nullifier collided across distinct bearers");
}

#[test]
fn test_verify_hash_commit_against_known_vector() {
    // Hardcoded SHA256 from an independent computation:
    //   python3 -c "import hashlib; print(hashlib.sha256(b'abcd' + b'\\x42' * 16).hexdigest())"
    //   -> 007d4d4455a6833206ac7c9459d56b966d797244476bb3b54ebacdef267ec13d
    //
    // Using a known-good vector rather than rebuilding it inside the test
    // means a bug in `verify_hash_commit`'s preimage layout (e.g. blinder
    // before plaintext, wrong length truncation) is caught, not masked.
    let plaintext: [u8; 4] = [0x61, 0x62, 0x63, 0x64];
    let blinder: [u8; BLINDER_LEN] = [0x42; BLINDER_LEN];
    let expected: [u8; 32] = [
        0x00, 0x7d, 0x4d, 0x44, 0x55, 0xa6, 0x83, 0x32, 0x06, 0xac, 0x7c, 0x94, 0x59, 0xd5, 0x6b,
        0x96, 0x6d, 0x79, 0x72, 0x44, 0x47, 0x6b, 0xb3, 0xb5, 0x4e, 0xba, 0xcd, 0xef, 0x26, 0x7e,
        0xc1, 0x3d,
    ];
    verify_hash_commit::<4, 20>(plaintext, 4, blinder, expected);
}

#[test(should_fail_with = "hash commit mismatch")]
fn test_verify_hash_commit_rejects_wrong_hash() {
    let plaintext: [u8; 4] = [0x61, 0x62, 0x63, 0x64];
    let blinder: [u8; BLINDER_LEN] = [0x42; BLINDER_LEN];
    let wrong: [u8; 32] = [0xff; 32];
    verify_hash_commit::<4, 20>(plaintext, 4, blinder, wrong);
}

#[test]
fn test_main_happy_path() {
    let mut bearer: [u8; MAX_BEARER_LEN] = [0; MAX_BEARER_LEN];
    for i in 0..22 {
        bearer[i] = 65; // 'A'
    }
    let blinder_token: [u8; BLINDER_LEN] = [0x42; BLINDER_LEN];
    let blinder_me: [u8; BLINDER_LEN] = [0x55; BLINDER_LEN];

    let mut p1: [u8; BEARER_HASH_INPUT_LEN] = [0; BEARER_HASH_INPUT_LEN];
    let mut p2: [u8; BEARER_HASH_INPUT_LEN] = [0; BEARER_HASH_INPUT_LEN];
    for i in 0..MAX_BEARER_LEN {
        if (i as u32) < 22 {
            p1[i] = bearer[i];
            p2[i] = bearer[i];
        }
    }
    for i in 0..BLINDER_LEN {
        p1[22 + i] = blinder_token[i];
        p2[22 + i] = blinder_me[i];
    }
    let h_token = sha256_var(p1, 22 + BLINDER_LEN);
    let h_me = sha256_var(p2, 22 + BLINDER_LEN);
    let null = compute_bearer_nullifier(bearer, 22);

    main(
        bearer,
        22,
        blinder_token,
        blinder_me,
        h_token,
        h_me,
        null,
        [0x11; 20],
        [0x22; 20],
    );
}

#[test(should_fail_with = "bearer too short")]
fn test_main_bearer_too_short_fails() {
    let bearer: [u8; MAX_BEARER_LEN] = [0; MAX_BEARER_LEN];
    let blinder_token: [u8; BLINDER_LEN] = [0x42; BLINDER_LEN];
    let blinder_me: [u8; BLINDER_LEN] = [0x55; BLINDER_LEN];
    let mut p1: [u8; BEARER_HASH_INPUT_LEN] = [0; BEARER_HASH_INPUT_LEN];
    let mut p2: [u8; BEARER_HASH_INPUT_LEN] = [0; BEARER_HASH_INPUT_LEN];
    for i in 0..BLINDER_LEN {
        p1[i] = blinder_token[i];
        p2[i] = blinder_me[i];
    }
    let h_token = sha256_var(p1, BLINDER_LEN);
    let h_me = sha256_var(p2, BLINDER_LEN);
    let null = compute_bearer_nullifier(bearer, 0);
    main(
        bearer,
        0,
        blinder_token,
        blinder_me,
        h_token,
        h_me,
        null,
        [0x11; 20],
        [0x22; 20],
    );
}

#[test(should_fail_with = "hash commit mismatch")]
fn test_main_wrong_bearer_hash_fails() {
    let mut bearer: [u8; MAX_BEARER_LEN] = [0; MAX_BEARER_LEN];
    for i in 0..22 {
        bearer[i] = 65;
    }
    let blinder_token: [u8; BLINDER_LEN] = [0x42; BLINDER_LEN];
    let blinder_me: [u8; BLINDER_LEN] = [0x55; BLINDER_LEN];
    let bad_h_token: [u8; 32] = [0xff; 32];
    let mut p2: [u8; BEARER_HASH_INPUT_LEN] = [0; BEARER_HASH_INPUT_LEN];
    for i in 0..MAX_BEARER_LEN {
        if (i as u32) < 22 {
            p2[i] = bearer[i];
        }
    }
    for i in 0..BLINDER_LEN {
        p2[22 + i] = blinder_me[i];
    }
    let h_me = sha256_var(p2, 22 + BLINDER_LEN);
    let null = compute_bearer_nullifier(bearer, 22);
    main(
        bearer,
        22,
        blinder_token,
        blinder_me,
        bad_h_token,
        h_me,
        null,
        [0x11; 20],
        [0x22; 20],
    );
}

#[test(should_fail_with = "bearer tail must be zero-padded")]
fn test_main_nonzero_tail_fails() {
    let mut bearer: [u8; MAX_BEARER_LEN] = [0; MAX_BEARER_LEN];
    for i in 0..22 {
        bearer[i] = 65;
    }
    bearer[50] = 0x99;
    let blinder_token: [u8; BLINDER_LEN] = [0x42; BLINDER_LEN];
    let blinder_me: [u8; BLINDER_LEN] = [0x55; BLINDER_LEN];
    let mut p1: [u8; BEARER_HASH_INPUT_LEN] = [0; BEARER_HASH_INPUT_LEN];
    let mut p2: [u8; BEARER_HASH_INPUT_LEN] = [0; BEARER_HASH_INPUT_LEN];
    for i in 0..22 {
        p1[i] = bearer[i];
        p2[i] = bearer[i];
    }
    for i in 0..BLINDER_LEN {
        p1[22 + i] = blinder_token[i];
        p2[22 + i] = blinder_me[i];
    }
    let h_token = sha256_var(p1, 22 + BLINDER_LEN);
    let h_me = sha256_var(p2, 22 + BLINDER_LEN);
    let null = compute_bearer_nullifier(bearer, 22);
    main(
        bearer,
        22,
        blinder_token,
        blinder_me,
        h_token,
        h_me,
        null,
        [0x11; 20],
        [0x22; 20],
    );
}
