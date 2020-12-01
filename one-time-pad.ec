(*Bitstrings ops, axioms taken from https://github.com/alleystoughton/EasyTeach - EasyCrypt teaching examples by @alleystoughton.*)

require import AllCore Distr.
      
(* minimal axiomatization of bitstrings *)

op n : int.  (* length of bitstrings *)

axiom ge0_n : 0 <= n.

type bits.  (* type of bitstrings *)

op zero : bits.  (* the all zero bitstring *)

op (^^) : bits -> bits -> bits.  (* pointwise exclusive or *)

axiom xorC (x y : bits) :
  x ^^ y = y ^^ x.

axiom xorA (x y z : bits) :
  x ^^ y ^^ z = x ^^ (y ^^ z).

axiom xor0_ (x : bits) :
  zero ^^ x = x.

lemma xor_0 (x : bits) :
  x ^^ zero = x.
proof.
  by rewrite xorC xor0_.
qed.

axiom xorK (x : bits) :
  x ^^ x = zero.

lemma xor_double_same_right (x y : bits) :
  x ^^ y ^^ y = x.
proof.
by rewrite xorA xorK xor_0.
qed.

lemma xor_double_same_left (x y : bits) :
  y ^^ y ^^ x = x.
proof.
rewrite xorC.
rewrite -xorA.
by rewrite xor_double_same_right.
qed.

(* uniform, full and lossless distribution on bitstrings *)

op dbits : bits distr.

axiom dbits_ll : is_lossless dbits.

axiom dbits1E (x : bits) :
  mu1 dbits x = 1%r / (2 ^ n)%r.

lemma dbits_fu : is_full dbits.
proof.
rewrite /is_full.
move => ?.
rewrite /support.
rewrite dbits1E.
rewrite RField.div1r.
rewrite StdOrder.RealOrder.invr_gt0.
rewrite lt_fromint. rewrite StdOrder.IntOrder.expr_gt0.
trivial.
qed.



(* Game based approach *)

module type MyADV = {
  proc * get() : bits
  proc guess_m(x : bits) : bool
}.


require import DBool.

module type ENC = {
  proc encrypt(m0 : bits, m1 : bits) : bits
}.

module Exp (Enc : ENC, Adv : MyADV) = {
  var i : bool
  
  proc main() : bool = {
    var m0, m1, c : bits;
    var b : bool;
    m0 <@ Adv.get();
    m1 <@ Adv.get();
    c <@ Enc.encrypt(m0, m1);
    b <@ Adv.guess_m(c);
    return b = i;
  }
}.

module Otp : ENC = {
  proc encrypt(m0 : bits, m1 : bits) : bits = {
    var c : bits;
    Exp.i <$ {0,1};
    c <$ dbits;
    return (Exp.i ? m0 : m1) ^^ c;
  }
}.

module Random : ENC = {
  proc encrypt(m0 : bits, m1 : bits) : bits = {
    var c : bits;
    Exp.i <$ {0,1};
    c <$ dbits;
    return c;
  }
}.


lemma ExpOtp_ExpRandom (Adv <: MyADV{Exp}):
  equiv[Exp(Otp, Adv).main ~ Exp(Random, Adv).main :
        true ==> ={res}].
proof.
proc.
seq 2 2: (={glob Adv}).
call (_ : true).
call (_ : true).
skip.
progress.
inline*.
sp.
seq 1 1 : (={glob Adv, glob Exp} /\ m00{1} = m0{1} /\ m10{1} = m1{1}).
rnd => //.
seq 1 1 : (={glob Adv, glob Exp} /\ (c0{1} ^^ (Exp.i{1} ? m0{1} : m1{1})) = c0{2} /\ m00{1} = m0{1} /\ m10{1} = m1{1}).
rnd (fun (m_ : bits) => m_ ^^ (Exp.i{1} ? m0{1} : m1{1})).
skip.
progress.
by rewrite xor_double_same_right.
by rewrite !dbits1E.
by apply dbits_fu.
by rewrite xor_double_same_right.
sp.
call (_ : true).
skip.
progress.
by rewrite xorC.
qed.


module DummyExp (Adv : MyADV) = {
  proc main() : bool = {
    var m0, m1, c : bits;
    var b, i : bool;
    m0 <@ Adv.get();
    m1 <@ Adv.get();
    i <$ {0,1};
    c <$ dbits;
    b <@ Adv.guess_m(c);
    return i;
  }
}.


lemma ExpRandom_ExpDummy (Adv <: MyADV{Exp}):
  equiv[Exp(Random, Adv).main ~ DummyExp(Adv).main :
        true ==> ={res}].
proof.
proc.
inline*.
seq 2 2: (={glob Adv}).
call (_: true) => //.
call (_: true) => //.
sp.
swap 1 2 3.
swap {1} 3 4 4.
seq 2 1: (={glob Adv, c} /\ c{1}=c0{1}).
wp. rnd. skip. progress.
seq 1 1  :(={glob Adv, c} /\ c{1}=c0{1}).
call (_ : true). skip. progress.
rnd (fun (j: bool) => (j = b{1})). skip.
(*smt would end the proof here *)
progress.
elim (iR).
elim (b{1}). auto. auto.
elim (b{1}). auto. auto.
elim (iL).
elim (b{1}). auto. auto.
elim (b{1}). auto. auto.
simplify.
rewrite (eq_sym b{1}). reflexivity.
qed.


module DummiestExp = {
  proc main() : bool = {
    var i : bool;
    i <$ {0,1};
    return i;
  }
}.

lemma Dummy_Dummiest (Adv <: MyADV) : 
   islossless Adv.get => islossless Adv.guess_m => 
     equiv[DummyExp(Adv).main ~ DummiestExp.main : true ==> ={res}].
proof.
move => ? ?.
proc.
seq 2 0 : true.
call {1} (_: true ==> true).
call {1} (_: true ==> true).
skip. auto.
seq 1 1: (={i}).
rnd. skip. auto.
seq 1 0 : (={i}).
rnd {1}. skip. progress. apply dbits_ll. 
call {1} (_: true ==> true). skip. trivial.
qed.


lemma Exp_dummiest_inv_2 &m : 
   Pr[DummiestExp.main() @ &m : res] = 1%r / 2%r.
  proof.
  byphoare.
  proc.
  rnd.
  skip. simplify.
  rewrite dboolE_count. simplify. rewrite /b2i. simplify. trivial.
  trivial. trivial.
qed.

lemma Exp_dummiest_dummy (Adv <: MyADV{Exp}) &m : 
    islossless Adv.get => islossless Adv.guess_m => 
    Pr[DummyExp(Adv).main() @ &m : res] = Pr[DummiestExp.main() @ &m : res].
  proof.
  move => ? ?.
  byequiv (Dummy_Dummiest Adv H H0). trivial. trivial.
qed.

lemma Exp_dummy_random (Adv <: MyADV{Exp}) &m : 
    Pr[Exp(Random, Adv).main() @ &m : res] = Pr[DummyExp(Adv).main() @ &m : res].
  proof.
  by byequiv (ExpRandom_ExpDummy Adv).
qed.

lemma ExpOpt_ExpRandom (Adv <: MyADV{Exp}) &m :
  Pr[Exp(Otp, Adv).main() @ &m : res] = Pr[Exp(Random, Adv).main() @ &m : res].
  proof.
by byequiv (ExpOtp_ExpRandom Adv).
qed.

(* Czy w takim razie mozna zakladac konkretny rozklad odpowiedzi Adv??*)

lemma ExpOtp_inv2 (Adv <: MyADV{Exp}) &m:
    islossless Adv.get => islossless Adv.guess_m => 
    Pr[Exp(Otp, Adv).main() @ &m : res] = 1%r / 2%r.
proof.
move => ? ?.
rewrite (ExpOpt_ExpRandom Adv) (Exp_dummy_random Adv) (Exp_dummiest_dummy Adv &m H H0).
by apply (Exp_dummiest_inv_2 &m).
qed.
