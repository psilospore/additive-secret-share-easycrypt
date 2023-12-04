
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

module O = {
  proc fst(shares : Share * Share) : Share = {
      var share1, share2;
      (share1, share2) <- shares;
      return share1;
  }
}.


lemma additive_secret_share2 (secret1 : Secret) (secret2 : Secret) (a: Share) : Pr[fst(AdditiveSecretShare.share(secret1)) = a] = Pr[fst(AdditiveSecretShare.share(secret2)) = a].

lemma G1_G2_true &m :
Pr[G1.f() @ &m : res] = Pr[G2.f() @ &m : res].

lemma G1_G2_true &m :
Pr[G1.f() @ &m : res] = Pr[G2.f() @ &m : res].
