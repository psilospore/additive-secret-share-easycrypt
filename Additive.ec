
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

(* Maybe try a simplier Probability example before proceeding?*)
(*lemma test_pr : Pr[] *)

lemma additive_secret_share2 (secret1 : Secret) (secret2 : Secret) (a: Share) : Pr[fst(AdditiveSecretShare.share(secret1)) = a] = Pr[fst(AdditiveSecretShare.share(secret2)) = a].

(* Useful to reference: *)

(* Maybe we need this format?*)
(*&m is memory*)
(*res is result*)
(*So this states given some memory &m G1.f() and G2.f() return true at about the same rate*)
lemma G1_G2_true &m :
Pr[G1.f() @ &m : res] = Pr[G2.f() @ &m : res].
