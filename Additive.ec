
require import DBool.
require import Int.
require import List.




require import PrimeField.

type Share = t.
type Secret = t.


module type Protocol2 = {
  proc share(secret: Secret): Share * Share
  proc reconstruct(shares: Share * Share): Secret
}.


module AdditiveSecret2Share: Protocol2 = {

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

(* This works but maybe is not the best way*)
(* Given two secrets and a share. The probability the first shares of each match a given share is equal. *)
lemma additive_secret_share2 &m (secret1 : Secret) (secret2 : Secret) (a: Share) :
    Pr [ AdditiveSecret2Share.share(secret1) @ &m : fst res = a ] =
    Pr [ AdditiveSecret2Share.share(secret2) @ &m : fst res = a ].
proof.
(* byequiv. *)
(* elim*. *)
admit.
qed.

(* Now let's extend it to n shares *)

(* A data structure to always ensure that there are two shares *)
type shares = [ LastTwoShares of Share & Share | ShareCons of Share & shares].

(* Example of construction*)
op lastTwo = LastTwoShares (ofint 3) (ofint 2).
op allShares = ShareCons (ofint 4) lastTwo.

module type ProtocolN = {
  proc share(secret: Secret, n: int): shares
  (*proc reconstruct(shares: shares): Secret*)
}.

module AdditiveSecretNShare: ProtocolN = {

  proc share(secret : Secret, n: int): shares = {
    var share1, share2, total;
    var shares_l : shares;

    while (2 <= n) {
      share1 <$ FDistr.dt;
      if (n = 2) {
        share2 <- secret - total;
        shares_l <- LastTwoShares share1 share2;
      }
      else {
        shares_l <- ShareCons share1 shares_l;
      }
    }
    return shares_l;
  }

}.


(* Stub for n secret sharing *)
lemma additive_secret_share_n &m (secret1 : Secret) (secret2 : Secret) (n : int) (s: shares) :
    Pr [ AdditiveSecretNShare.share(secret1, n) @ &m : res = s] =
    Pr [ AdditiveSecretNShare.share(secret2, n) @ &m : res = s].
proof.
admit.
qed.

(* Random Stuff below*)
(* How do we get the first element? Like this: *)
lemma test_fst : fst (3, 2) = 3.
proof.
trivial.
qed.



(* Useful to reference: *)

(* Maybe we need this format?*)
(*&m is memory*)
(*res is result*)
(*So this states given some memory &m G1.f() and G2.f() return true at about the same rate*)
