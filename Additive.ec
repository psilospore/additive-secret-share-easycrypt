
require import DBool.

require import PrimeField.

type Share = t.
type Secret = t.

module type Protocol = {
  proc share(secret: Secret): Share * Share
  proc reconstruct(shares: Share * Share): Secret
}.

module AdditiveSecretShare: Protocol = {

  proc share(secret : Secret): Share * Share = {
    var share1, share2;

    share1 <$ FDistr.dt;

    share2 <- secret - share1;

    return (share1, share2);
  }

  (* I didn't know how to get the first share in the lemma so just made this*)
  proc fst_share(secret : Secret): Share = {
    var share1, share2;
    (share1, share2) <@ share(secret);
    return share1;
  }

  proc fst_share_is_value(secret : Secret, expected_share : Share): bool = {
    var share1, share2;
    (share1, share2) <@ share(secret);
    return (share1 = expected_share);
  }

  proc reconstruct(shares : Share * Share): Secret = {
    var secret;
    var share1, share2;

    (share1, share2) <- shares;
    secret <- share1 + share2;

    return (secret);
  }

}.

(* How do we get the first element? Like this: *)
lemma test_fst : fst (3, 2) = 3.
proof.
trivial.
qed.


(* This works but maybe is not the best way*)
(* Given two secrets and a share. The probability the first shares of each match a given share is equal. *)
lemma additive_secret_share2 &m (secret1 : Secret) (secret2 : Secret) (a: Share) :
    Pr [ AdditiveSecretShare.share(secret1) @ &m : fst res = a ] =
    Pr [ AdditiveSecretShare.share(secret2) @ &m : fst res = a ].

(* I think this doesn't work for us*)
lemma additive_secret_share4 &m (secret1 : Secret) (secret2 : Secret) (a: Share) :
    equiv [ AdditiveSecretShare.share ~ AdditiveSecretShare.share : ={A} ==> res{1} = res{2} ].



(* Useful to reference: *)

(* Maybe we need this format?*)
(*&m is memory*)
(*res is result*)
(*So this states given some memory &m G1.f() and G2.f() return true at about the same rate*)
lemma G1_G2_true &m :
Pr[G1.f() @ &m : res] = Pr[G2.f() @ &m : res].
