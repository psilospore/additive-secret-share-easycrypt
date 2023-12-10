
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
lemma additive_secret_share2_fst &m (secret1 : Secret) (secret2 : Secret) (a: Share) :
    Pr [ AdditiveSecret2Share.share(secret1) @ &m : fst res = a ] =
    Pr [ AdditiveSecret2Share.share(secret2) @ &m : fst res = a ].
proof.
byequiv.
elim*.
proc .
auto.
auto.
auto.
qed.

lemma additive_secret_share2_snd &m (secret1 : Secret) (secret2 : Secret) (a: Share) :
    Pr [ AdditiveSecret2Share.share(secret1) @ &m : snd res = a ] =
    Pr [ AdditiveSecret2Share.share(secret2) @ &m : snd res = a ].
proof.
admit.
qed.


(* Now let's extend it to n shares *)

(* A data structure to always ensure that there are two shares *)
type shares = [ LastTwoShares of Share & Share | ShareCons of Share & shares].

(* Example of construction*)
op lastTwo = LastTwoShares (ofint 3) (ofint 2).
op allShares = ShareCons (ofint 4) lastTwo.

module type ProtocolN = {
  proc share(secret: Secret, n: int): Share list
  (*proc reconstruct(shares: shares): Secret*)
}.

module AdditiveSecretNShare: ProtocolN = {

  proc share(secret : Secret, n: int): Share list = {
    var random_share, final_share, total;
    var shares_l : Share list;

    shares_l <- [];
    total <- ofint 0;

    while (2 <= n) {
      random_share <$ FDistr.dt;
      shares_l <- shares_l ++ [random_share];
      total <- total + random_share;
      if (n = 2) {
        final_share <- secret - total;
        shares_l <- shares_l ++ [final_share];
      }
      n <- n - 1;
    }
    return shares_l;
  }

}.


(* Stub for n secret sharing *)
lemma additive_secret_share_n &m (secret1 : Secret) (secret2 : Secret) (n : int) (s: Share list) :
    Pr [ AdditiveSecretNShare.share(secret1, n) @ &m : res = s] =
    Pr [ AdditiveSecretNShare.share(secret2, n) @ &m : res = s].
proof.
byequiv.
proc.
admit.
auto.
auto.
qed.

(* Random Stuff below*)

(* How do we get the first element? Like this: *)
lemma test_fst : fst (3, 2) = 3.
proof.
trivial.
qed.
