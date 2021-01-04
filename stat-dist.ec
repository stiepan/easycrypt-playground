require import Bool AllCore List Finite Discrete Distr DBool Logic.
require import StdRing StdOrder StdBigop RealLub RealSeq RealSeries Bigalg.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import Ring.IntID IntOrder RField RealOrder Number.
require (*--*) BitWord.


abstract theory Sdist.
type X.

clone include MFinite
  with type t <- X
  rename "dunifinE" as "dunifxE_count"
  rename "dunifin" as "dunifx".


op delta_d (da : X distr, db : X distr) : real = (inv 2%r) * big predT (fun x => `|mu1 da x - mu1 db x|) (Support.enum).

op d (da : X distr) : real = delta_d da dunifx.


lemma big_sym (da : X distr) (db : X distr) : is_lossless da => is_lossless db => big (fun x => mu1 da x > mu1 db x) (fun x => mu1 da x - mu1 db x) (Support.enum) = big (fun x => mu1 da x <= mu1 db x) (fun x => mu1 db x - mu1 da x) (Support.enum).
proof.
move => ? ?.
rewrite -subr_eq0 sumrN => //=.
have ineqC : (fun x => mu1 da x <= mu1 db x) = predC (fun x => mu1 da x > mu1 db x).
apply fun_ext. rewrite /(==).
move => ?. rewrite /predC ltr_def.
rewrite negb_and => //=. smt.
rewrite ineqC.
have _substr : (fun (x : X) => - (mu1 db x - mu1 da x)) = (fun (x : X) => mu1 da x - mu1 db x).
apply fun_ext. rewrite /(==). move => ?.
rewrite opprB => //.
rewrite _substr -bigEM big_split-sumrN.
have mu1_as_mass: (fun (i : X) => mu1 da i) = (fun (i : X) => mass da i).
apply fun_ext. rewrite /(==). move => ?.
rewrite massE => //.
have enum_uniq : Support.enum = undup (Support.enum).
rewrite undup_id.
apply Support.enum_uniq. trivial. rewrite enum_uniq.
rewrite -(mu_mem da Support.enum) -(mu_mem db Support.enum).
have all_mem: mem Support.enum = predT.
rewrite /predT. apply fun_ext. rewrite /(==).
move => ?. rewrite (Support.enumP x) => //.
rewrite all_mem.
rewrite !is_losslessP => //.
qed.

lemma delta_d_alt (da : X distr, db : X distr) : is_lossless da => is_lossless db => delta_d da db = big (fun x => mu1 da x > mu1 db x) (fun x => mu1 da x - mu1 db x) (Support.enum).
proof.
move => ? ?.
rewrite /delta_d.
rewrite {1} (bigEM (fun (x : X) => mu1 da x > mu1 db x)).
rewrite {1} big_mkcond => //=.
have mod_if : (fun (i : X) =>
      if mu1 db i < mu1 da i then `|mu1 da i - mu1 db i| else 0%r) = (fun (i : X) => if mu1 db i < mu1 da i then mu1 da i - mu1 db i else 0%r).
apply fun_ext. rewrite /(==). move => ?.
case (mu1 db x < mu1 da x). smt. auto.
rewrite mod_if. rewrite -{1} big_mkcond.
have ineqC : (fun x => mu1 db x >= mu1 da x) = predC (fun x => mu1 db x < mu1 da x).
apply fun_ext. rewrite /(==).
move => ?. rewrite /predC. smt.
rewrite -ineqC.
have mod_pred : (big (fun (x : X) => mu1 da x <= mu1 db x)
   (fun (x : X) => `|mu1 da x - mu1 db x|) Support.enum) = (big (fun (x : X) => mu1 da x <= mu1 db x)
   (fun (x : X) => mu1 db x - mu1 da x) Support.enum).
rewrite big_mkcond => //=.
have mod_pred_ : (fun (i : X) =>
      if mu1 da i <= mu1 db i then `|mu1 da i - mu1 db i| else 0%r) = (fun (i : X) => if mu1 da i <= mu1 db i then mu1 db i - mu1 da i else 0%r).
apply fun_ext. rewrite /(==). move => ?.
case (mu1 da x <= mu1 db x).
move => ?. rewrite -normrN. smt. auto.
rewrite mod_pred_ -big_mkcond. reflexivity.
rewrite mod_pred.
rewrite big_sym => //. smt. (*alebra tactic works here, but what exactly it does*)
qed.


lemma delta_dmap_f (f : X -> X) : forall (da : X distr), is_lossless da => forall (db : X distr), is_lossless db => 
    big predT (fun (x : X) => `|mu1 (dmap da f) x - mu1 (dmap db f) x|) Support.enum = 
    big predT (fun (x : X) => `|big (fun (x0 : X) => f x0 = x) (fun (x0 : X) => mu1 da x0 - mu1 db x0) Support.enum|) Support.enum.
proof.
move => ? ? ? ?.
have dmap_expand : (fun (x : X) => `|mu1 (dmap da f) x - mu1 (dmap db f) x|) = (fun (x : X) => `|big predT (fun (x0 : X) => if f x0 = x then mu1 da x0 else 0%r) Support.enum - big predT (fun (x0 : X) => if f x0 = x then mu1 db x0 else 0%r) Support.enum|).
rewrite fun_ext /(==) => ?.
rewrite !dmap1E !/(\o) !muE => //.
rewrite {1 2}/pred1.
rewrite (sumE_fin (fun (x0 : X) => if f x0 = x then mass da x0 else 0%r) (Support.enum) Support.enum_uniq) => [ ? ? | //]. apply (Support.enumP x0).
rewrite (sumE_fin (fun (x0 : X) => if f x0 = x then mass db x0 else 0%r) (Support.enum) Support.enum_uniq) => [ ? ? | //]. apply (Support.enumP x0).
have mass_mu1 : forall (d : X distr), true => (fun (x0 : X) => if f x0 = x then mass d x0 else 0%r) = (fun (x0 : X) => if f x0 = x then mu1 d x0 else 0%r).
move => ? _.
rewrite fun_ext /(==) => ?.
rewrite massE => //.
rewrite !mass_mu1 => //.
rewrite dmap_expand.
have merge_sum : (fun (x : X) =>
     `|big predT (fun (x0 : X) => if f x0 = x then mu1 da x0 else 0%r)
         Support.enum -
       big predT (fun (x0 : X) => if f x0 = x then mu1 db x0 else 0%r)
         Support.enum|) = (fun (x : X) =>
     `|big (fun (x0 : X) => f x0 = x) (fun (x0 : X) => mu1 da x0 - mu1 db x0)
         Support.enum|).
rewrite fun_ext /(==) => ?.
rewrite sumrN => //=.
have move_min_inside : (fun (x0 : X) => - (if f x0 = x then mu1 db x0 else 0%r)) = (fun (x0 : X) => (if f x0 = x then - (mu1 db x0) else 0%r)).
rewrite fun_ext /(==) => ?.
by case (f x0 = x).
rewrite move_min_inside.
rewrite -big_mkcond -big_mkcond -big_split => //=; auto.
rewrite merge_sum => //.
qed.


lemma ex3_inq : forall (f : X -> X), true => forall (da : X distr), is_lossless da => forall (db : X distr), is_lossless db => delta_d (dmap da f) (dmap db f) <= delta_d da db.
move => ? ? ? ? ? ?.
rewrite /delta_d.
rewrite ler_pmul2l. apply invr_gt0 => //=.
rewrite delta_dmap_f => //.
have triangle : big predT (fun (x : X) => 
    `|big (fun (x0 : X) => f x0 = x) (fun (x0 : X) => mu1 da x0 - mu1 db x0) Support.enum|) Support.enum <= big predT (fun (x : X) =>
     big (fun (x0 : X) => f x0 = x) (fun (x0 : X) => `|mu1 da x0 - mu1 db x0|)
         Support.enum) Support.enum.
apply ler_sum => [? ?] => //=.
apply big_normr.
have partition : (big predT (fun (x : X) =>
     big (fun (x0 : X) => f x0 = x) (fun (x0 : X) => `|mu1 da x0 - mu1 db x0|)
         Support.enum) Support.enum) = (big predT (fun (x : X) => `|mu1 da x - mu1 db x|) Support.enum).
rewrite (partition_big f predT predT (fun (x0 : X) => `|mu1 da x0 - mu1 db x0|) (Support.enum) (Support.enum)). by apply Support.enum_uniq.
move => ? ? ?. split.
apply Support.enumP.
rewrite /predT => //=. trivial.
rewrite -partition.
by apply triangle.
qed.


lemma eq_l_size : forall (f : X -> X), injective f => forall (xs : X list), true => size (map f xs) = size xs.
proof.
move => f f_inj xs true_ {true_}.
elim xs.
simplify. trivial.
move => x l IH.
(*smt*)
have map_exp : map f (x :: l) = (f x) :: (map f l); trivial.
rewrite map_exp.
have x_l : size (x :: l) = 1 + size l; trivial.
have fx_fl : size (f x :: map f l) = 1 + size (map f l); trivial.
rewrite x_l fx_fl IH => //.
qed.


lemma uniq_map_support : forall (f : X -> X), injective f => uniq (map f Support.enum).
proof.
move => f f_inj.
apply map_inj_in_uniq.
move => x y x_in y_in {x_in y_in}.
exact f_inj.
exact Support.enum_uniq.
qed.


lemma whole_sup_map : forall (f : X -> X), injective f => forall (x : X), true => mem (map f Support.enum) x.
move => f f_inj x x_ {x_}.
have mem_eq_and_size : (forall x, mem (map f Support.enum) x <=> mem Support.enum x) /\ size (map f Support.enum) = size Support.enum.
apply leq_size_perm.
by exact/uniq_map_support.
rewrite /(<=).
move => x_X x_in_map {x_in_map}.
by exact/Support.enumP.
rewrite (eq_l_size f f_inj) => //.
elim mem_eq_and_size.
move => mem_eq eq_size {eq_size}.
apply (mem_eq x).
by exact/Support.enumP.
qed.


lemma perm_eq_supp : forall (f : X -> X), injective f => perm_eq (map f Support.enum) Support.enum.
proof.
move => f f_inj.
rewrite /perm_eq allP => //=.
move => x x_in_sup {x_in_sup}.
rewrite count_uniq_mem. exact (uniq_map_support f f_inj).
rewrite count_uniq_mem. exact (Support.enum_uniq).
rewrite Support.enumP (whole_sup_map f f_inj) => //.
qed.


lemma ex3_eq (f : X -> X, da, db : X distr) : injective f =>  is_lossless da => is_lossless db => delta_d (dmap da f) (dmap db f) = delta_d da db.
proof.
move => inj_f da_ll db_ll.
rewrite /delta_d.
have -> : forall (x, y, z : real), x <> 0%r => x * y = x * z <=> y = z.
smt. rewrite invr_eq0 => //=.
rewrite delta_dmap_f => //.
rewrite -(eq_big_perm predT ((fun (x : X) =>
     `|big (fun (x0 : X) => f x0 = x) (fun (x0 : X) => mu1 da x0 - mu1 db x0)
         Support.enum|)) (map f Support.enum) Support.enum).
by exact perm_eq_supp.
rewrite big_map /(\o).
have predT_composed : (fun (x : X) => predT (f x)) = predT.
rewrite fun_ext /(==) => x.
rewrite /predT => //.
rewrite predT_composed.
have fun_eq : (fun (x : X) => `|mu1 da x - mu1 db x|) = (fun (x : X) =>
     `|big (fun (x0 : X) => f x0 = f x)
         (fun (x0 : X) => mu1 da x0 - mu1 db x0) Support.enum|).
rewrite fun_ext /(==) => x.
have cond_pred1 : (fun (x0 : X) => f x0 = f x) = fun (x0 : X) => x0 = x.
rewrite fun_ext /(==) => x0.
case (x0 = x).
move => eq_x0_x.
rewrite eqT.
congr.
move => neq_x0_x.
rewrite neqF.
have inj_f_transposed : forall (x1, x2 : X), x1 <> x2 => f x1 <> f x2.
move => x1 x2.
rewrite -implybNN => //=.
apply (inj_f x1 x2).
apply inj_f_transposed. apply neq_x0_x.
rewrite cond_pred1.
rewrite -big_filter.
have singleton : filter (transpose (=) x) Support.enum = [x].
rewrite filter_pred1.
rewrite Support.enum_spec. rewrite nseq1. trivial.
rewrite singleton.
rewrite big_seq1 => //=.
rewrite fun_eq.
reflexivity.
qed.

lemma ex4_triangle (db, da, dc : X distr) : delta_d da dc <= delta_d da db + delta_d db dc.
proof.
rewrite /delta_d -mulrDr (ler_pmul2l (inv 2%r)); [by rewrite invr_gt0 | rewrite -big_split].
apply ler_sum => //= => x predTx {predTx}.
apply (ler_trans `|mu1 da x - mu1 db x + mu1 db x - mu1 dc x|); smt.
qed.

lemma ex4_symm (da, db : X distr) : delta_d da db = delta_d db da.
proof.
rewrite /delta_d; congr; congr; rewrite fun_ext /(==) => x; by rewrite distrC.
qed.

end Sdist.


op n : int.
axiom gt0_n : 0 < n.


clone import BitWord as Bits with
  op n <- n
proof gt0_n by exact/gt0_n
rename
  "word" as "bits"
  "dunifin" as "dbits".


clone import Sdist as Sbits with type X <- bits.


module type ADV = {
  proc messages() : bits * bits
  proc guess(x : bits) : bool
}.

op select_d (da, db : bits distr, b : bool) : bits distr = if !b then da else db.


module Exp(Adv : ADV) = {

  proc main(da, db : bits distr) : bool = {
    var b, ba : bool;
    var d : bits distr;
    var x : bits;
    b <$ {0,1};
    d <- select_d da db b;
    x <$ d;
    ba <- Adv.guess(x);
    return ba = b;
  }
}.


(* I'd like to provide exact bound for probability of adversary Adv success with expression that involves expressions Pr[Adv.guess(x) @ &m : res], this however doesn't seem to be possible, because rnd and seq tactics raised assertion errors with pHL statements of that sort. That's why I want to replace Adversary.guess with its "semantics", i.e. a function from inputs to distribuiton on outputs. *)
module Sampling(Adv : ADV) = {

  var adv_distr : bits -> bool distr (* aimed as Adv.guess semantics *)
  var x : bits

  proc sample(x : bits) : bool = {
    var b_ : bool;
    b_ <$ adv_distr x;
    return b_;
  }

  proc select(da, db : bits distr, b : bool) : bool = {
    var ba : bool;
    var d : bits distr;
    d <- select_d da db b;
    x <$ d;
    ba <@ sample(x);
    return ba = b;
  }

  proc main(da, db : bits distr) : bool = {
    var b, r : bool;
    b <$ {0,1};
    r <@ select(da, db, b);
    return r;
  }
}.

axiom is_adv_distr (Adv <: ADV) &m1 &m2 (x : bits) (b : bool): (glob Adv){m1} = (glob Adv){m2} => (Pr[Adv.guess(x) @ &m1 : res = b]) = mu1 (Sampling.adv_distr{m2} x) b.


section.

declare module Adv : ADV{Sampling}.

axiom Adv_ll : islossless Adv.guess.

lemma dist_select &m (da_p, db_p : bits distr, b_p : bool): uniq Support.enum => phoare [Sampling(Adv).select : Sampling.adv_distr{m} = Sampling.adv_distr{hr} /\ b = b_p /\ da = da_p /\ db = db_p ==> res /\ Sampling.x \in Support.enum] = (big predT (fun x_ => mu1 (Sampling.adv_distr{m} x_) b_p * mu1 (select_d da_p db_p b_p) x_) Support.enum).
proof.
elim: Support.enum => [ //= |x_bits lst ih]; simplify. rewrite big_nil; auto.
move => is_uniq.
phoare split (mu1 (Sampling.adv_distr{m} x_bits) b * mu1 (select_d da_p db_p b) x_bits) (big predT (fun (x_ : bits) => mu1 (Sampling.adv_distr{m} x_) b_p * mu1 (select_d da_p db_p b_p) x_) lst) : (Sampling.x = x_bits); progress.
proc.
sp; inline Sampling(Adv).sample; wp.
seq 1 : (Sampling.x = x_bits) (mu1 (select_d da_p db_p b) x_bits) (mu1 (Sampling.adv_distr{m} x_bits) b) (1%r - mu1 (select_d da_p db_p b) x_bits) 0%r (Sampling.adv_distr{m} = Sampling.adv_distr{hr}) => //=.
rnd; skip; progress.
rnd; skip; progress.
sp; rnd; skip; progress.
sp; rnd; skip; progress.
rewrite mu0_false; progress; rewrite negb_and; left; assumption.
progress; algebra.
conseq (:Sampling.adv_distr{m} = Sampling.adv_distr /\ b = b_p /\ da = da_p /\ db = db_p ==> res /\ Sampling.x \in lst).
progress.
elim H1. progress. apply implyFb; apply H.
trivial.
elim is_uniq => x_not_in uniq_list {uniq_list}.
apply (contraNneq (x_bits \in lst)). move => x_x_bit_eq.
rewrite -x_x_bit_eq; assumption. assumption.
right; assumption.
apply ih.
elim is_uniq. trivial.
qed.

lemma disting_exact &m (da_p, db_p : bits distr) : phoare [Sampling(Adv).main : Sampling.adv_distr{m} = Sampling.adv_distr{hr} /\ da = da_p /\ db = db_p ==> res] = ((inv 2%r * big predT (fun x => mu1 (Sampling.adv_distr{m} x) false * mu1 da_p x) Support.enum) + (inv 2%r * big predT (fun x => mu1 (Sampling.adv_distr{m} x) true * mu1 db_p x) Support.enum)).
proof.
proc.
seq 1 : (b = false) (inv 2%r) ( big predT (fun x => mu1 (Sampling.adv_distr{m} x) false * mu1 da_p x) Support.enum) (inv 2%r) (big predT (fun x => mu1 (Sampling.adv_distr{m} x) true * mu1 db_p x) Support.enum) (Sampling.adv_distr{m} = Sampling.adv_distr{hr} /\ da = da_p /\ db = db_p) => //=.
rnd; skip; progress.
rnd; skip; progress; rewrite dboolE_count => //=; rewrite /b2i => //=.
call (dist_select &m da_p db_p false). by exact/Support.enum_uniq.
skip; progress. by exact Support.enumP.
rnd; skip; progress.
rewrite dboolE_count => //=; rewrite /b2i => //=.
conseq (: Sampling.adv_distr{m} = Sampling.adv_distr{hr} /\ da = da_p /\ db = db_p /\ b = true ==> r); progress. rewrite neqF in H. rewrite eqT negbNE; assumption.
call (dist_select &m da_p db_p true). by exact/Support.enum_uniq.
skip; progress. by exact Support.enumP.
qed.

lemma disting_delta_bound (da_p, db_p : bits distr) : is_lossless da_p => is_lossless db_p => phoare [Sampling(Adv).main : (forall (x : bits), is_lossless (Sampling.adv_distr x)) /\ da = da_p /\ db = db_p ==> res] <= ((inv 2%r) * (1%r + delta_d da_p db_p)).
move => da_ll db_ll.
bypr.
move => &m [adv_distr_ll [sampling_da sampling_db]].
have -> : Pr[Sampling(Adv).main(da{m}, db{m}) @ &m : res] = ((inv 2%r * big predT (fun x => mu1 (Sampling.adv_distr{m} x) false * mu1 da_p x) Support.enum) + (inv 2%r * big predT (fun x => mu1 (Sampling.adv_distr{m} x) true * mu1 db_p x) Support.enum)).
byphoare (disting_exact &m da_p db_p) => //=.
pose x_false_s := big predT (fun (x : bits) => mu1 (Sampling.adv_distr{m} x) false * mu1 da_p x) Support.enum.
pose x_true_s := big predT (fun (x : bits) => mu1 (Sampling.adv_distr{m} x) true * mu1 db_p x) Support.enum.
have -> : (inv 2%r * x_false_s + inv 2%r * x_true_s <= inv 2%r * (1%r + delta_d da_p db_p)) <=> (x_false_s + x_true_s <= (1%r + delta_d da_p db_p)).
smt.
rewrite /x_false_s /x_true_s delta_d_alt; [exact da_ll | exact db_ll | trivial].
have adv_ft : forall (x : bits), mu1 (Sampling.adv_distr{m} x) true = 1%r - mu1 (Sampling.adv_distr{m} x) false.
move => x.
rewrite -subr_eq opprK.
rewrite -mu_disjoint /pred0 /predI /pred1 /(<=) => //=.
move => a. rewrite negb_and; case a; progress.
rewrite /predU.
have -> : (fun (x0 : bool) => x0 = true \/ x0 = false) = predT.
rewrite fun_ext /(==) => x0; rewrite /predT; case x0; progress.
exact (adv_distr_ll x).
have -> : (fun (x : bits) => mu1 (Sampling.adv_distr{m} x) true * mu1 db_p x) = fun (x : bits) => mu1 db_p x - mu1 (Sampling.adv_distr{m} x) false * mu1 db_p x.
rewrite fun_ext /(==) => x.
rewrite adv_ft. smt.
rewrite big_split.
have -> : big predT (fun (i : bits) => mu1 db_p i) Support.enum = 1%r.
have -> : big predT (fun (i : bits) => mu1 db_p i) Support.enum = weight db_p.
rewrite muE. rewrite (sumE_fin<:bits> (fun (x : bits) => if predT x then mass db_p x else 0%r) (Support.enum)). exact Support.enum_uniq. progress. exact Support.enumP.
have -> : (fun (x : bits) => mass db_p x) = fun (i : bits) => mu1 db_p i.
rewrite /predT fun_ext /(==) => x; simplify. rewrite massE. trivial. trivial.
exact db_ll.
rewrite -/x_false_s.
have -> : (x_false_s + (1%r + big predT (fun (i : bits) => - mu1 (Sampling.adv_distr{m} i) false * mu1 db_p i) Support.enum) <= 1%r + big (fun (x : bits) => mu1 db_p x < mu1 da_p x) (fun (x : bits) => mu1 da_p x - mu1 db_p x) Support.enum) <=> (x_false_s + big predT (fun (i : bits) => - mu1 (Sampling.adv_distr{m} i) false * mu1 db_p i) Support.enum <=
big (fun (x : bits) => mu1 db_p x < mu1 da_p x)
  (fun (x : bits) => mu1 da_p x - mu1 db_p x) Support.enum).
smt.
rewrite /x_false_s.
rewrite -big_split => //=.
have -> : (fun (i : bits) => mu1 (Sampling.adv_distr{m} i) false * mu1 da_p i - mu1 (Sampling.adv_distr{m} i) false * mu1 db_p i) = fun (x : bits) => mu1 (Sampling.adv_distr{m} x) false * (mu1 da_p x - mu1 db_p x).
rewrite fun_ext /(==) => x. rewrite mulrDr mulrN; trivial.
apply (ler_trans (big predT (fun (x : bits) => if mu1 db_p x < mu1 da_p x then mu1 (Sampling.adv_distr{m} x) false * (mu1 da_p x - mu1 db_p x) else 0%r) Support.enum)).
apply ler_sum. rewrite /predT => //=. move => a.
case (mu1 db_p a < mu1 da_p a); trivial.
move => db_db_nl.
smt (ge0_mu).
rewrite -big_mkcond.
apply ler_sum => //= => x mu1_db_lt_da.
smt (ge0_mu).
qed.

lemma adv_distr_ll &m (x : bits) : is_lossless (Sampling.adv_distr{m} x).
proof.
rewrite /is_lossless.
(*have -> : weight (adv_distr x) = mu (adv_distr x) predT.*)
have -> : predT = predU (pred1 true) (pred1 false).
rewrite /predT /predU /pred1 fun_ext /(==) => b0; case b0; progress.
rewrite mu_disjoint.
rewrite /predI /pred1 /pred0 /(<=) => a; case a; progress.
rewrite -(is_adv_distr Adv &m &m); trivial. rewrite -(is_adv_distr Adv &m &m); trivial.
have -> : (Pr[Adv.guess(x) @ &m : res = true] + Pr[Adv.guess(x) @ &m : res = false]) = Pr[Adv.guess(x) @ &m : res = true \/ res = false].
rewrite Pr[mu_disjoint]; progress; case (res{hr}); progress.
have -> : Pr[Adv.guess(x) @ &m : res = true \/ res = false] = Pr[Adv.guess(x) @ &m : true].
rewrite Pr[mu_eq]; progress; case (res{hr}); progress.
byphoare; trivial. by exact Adv_ll.
qed.

lemma adv_distr_eq : equiv[Exp(Adv).main ~ Sampling(Adv).main : ={glob Adv, da, db} ==> ={res}].
proof.
proc.
inline Sampling(Adv).select.
seq 3 6 : (={b, d, glob Adv} /\ x{1} = Sampling.x{2} /\ b{2} = b0{2}).
rnd; wp; rnd; skip => //=.
wp.
call (: ={x, glob Adv} ==> ={res}); trivial.
bypr (res){1} (res){2} => //=.
progress.
have sample_pr_mu1 : Pr[Sampling(Adv).sample(x{2}) @ &2 : res = a] = mu1 (Sampling.adv_distr{2} x{2}) a.
byphoare (: x{hr} = x{1} /\ Sampling.adv_distr{hr} = Sampling.adv_distr{2} ==> res = a).
proc.
rnd. skip. progress. rewrite H. progress. rewrite eq_sym. assumption. auto.
rewrite sample_pr_mu1.
rewrite (is_adv_distr Adv &1 &2); trivial. rewrite H.
trivial.
qed.

lemma adv_success_bound &m (da_p, db_p : bits distr) : is_lossless da_p => is_lossless db_p => Pr[Exp(Adv).main(da_p, db_p) @ &m : res] <= ((inv 2%r) * (1%r + delta_d da_p db_p)).
move => da_ll db_ll.
have -> : Pr[Exp(Adv).main(da_p, db_p) @ &m : res] = Pr[Sampling(Adv).main(da_p, db_p) @ &m : res].
byequiv (: ={glob Adv, da, db} ==> ={res}); auto; progress. by exact adv_distr_eq. 
byphoare (: (forall (x : bits), is_lossless (Sampling.adv_distr x)) /\ da{hr} = da_p /\ db{hr} = db_p ==> res); simplify; trivial.
apply (disting_delta_bound); [exact da_ll | exact db_ll].
apply (adv_distr_ll &m).
qed.

end section.


lemma ex2 (Adv <: ADV{Sampling}) &m (da_p, db_p : bits distr): islossless Adv.guess => is_lossless da_p => is_lossless db_p => Pr[Exp(Adv).main(da_p, db_p) @ &m : res] <= ((inv 2%r) * (1%r + delta_d da_p db_p)).
proof.
move => adv_ll.
apply (adv_success_bound Adv adv_ll &m da_p db_p).
qed.

op dkey : bits distr.

axiom dkey_ll : is_lossless dkey.

op mkey (x : bits) : bits distr = dmap dkey ((+^) x).


module Otp(Adv : ADV) = {

  var m0, m1 : bits

  proc exp(m0, m1 : bits) : bool = {
    var b, ba : bool;
    var k, m, x : bits;
    b <$ {0,1};
    m <- if !b then m0 else m1;
    k <$ dkey;
    x <- k +^ m;
    ba <- Adv.guess(x);
    return ba = b;
  }
  
  proc main() : bool = {
    var b_ : bool;
    (m0, m1) <@ Adv.messages();
    b_ <@ exp(m0, m1);
    return b_;
  }
  
}.

lemma inv_xor (x, y : bits) : x = y +^ (y +^ x).
by rewrite xorwA xorwK xorwC xorw0.
qed.

lemma inj_xor (x : bits) : injective ((+^) x).
proof.
rewrite /injective => x0 y.
by exact (WRing.addrI x x0 y).
qed.

lemma otp_exp_exp_main_eq (Adv <: ADV{Sampling}) : equiv[Exp(Adv).main ~ Otp(Adv).exp : ={glob Adv} /\ da{1} = mkey m0{2} /\ db{1} = mkey m1{2} ==> ={res}].
proc.
seq 1 1 : (={b, glob Adv} /\ da{1} = mkey m0{2} /\ db{1} = mkey m1{2}).
rnd; skip; progress.
seq 2 3 : (={b, x, glob Adv} /\ da{1} = mkey m0{2} /\ db{1} = mkey m1{2}).
sp; wp; rnd (fun (x : bits) => m{2} +^ x); skip. progress.
rewrite xorwA xorwK xorwC xorw0; trivial.
rewrite /select_d.
have l_xor : forall (m : bits), (fun (x : bits) => m +^ x = m +^ kR) = (transpose (=) kR).
move => m; rewrite fun_ext /(==) => x; rewrite eqboolP; split => eq. 
rewrite (WRing.addrI m x kR); trivial.
congr; assumption.
rewrite /mkey; case (b{2}); progress; rewrite dmap1E /(\o) /pred1 l_xor; trivial.
have ex_dkey : exists a, a \in dkey /\ xL = ((+^) (if !b{2} then m0{2} else m1{2})) a.
apply supp_dmap. case (!b{2}) => [b_ | b_]; simplify; smt.
elim ex_dkey; progress; rewrite xorwA xorwK xorwC xorw0; trivial.
by apply inv_xor.
by rewrite xorwC.
call (: true); skip; progress.
qed.

lemma otp_exp_eq (Adv <: ADV{Sampling}) (m0_p, m1_p : bits): islossless Adv.guess => phoare[Otp(Adv).exp : m0 = m0_p /\ m1 = m1_p ==> res] <= ((inv 2%r) * (1%r + delta_d (mkey m0_p) (mkey m1_p))).
proof.
move => adv_ll.
bypr => &m [m0_eq m1_eq].
have -> : Pr[Otp(Adv).exp(m0{m}, m1{m}) @ &m : res] = Pr[Exp(Adv).main(mkey m0_p, mkey m1_p) @ &m : res].
byequiv (: ={glob Adv} /\ da{2} = mkey m0{1} /\ db{2} = mkey m1{1}  ==> ={res}); trivial.
symmetry; conseq (: ={glob Adv} /\ da{1} = mkey m0{2} /\ db{1} = mkey m1{2} ==> ={res}); progress. exact (otp_exp_exp_main_eq Adv).
progress; trivial; [rewrite m0_eq | rewrite m1_eq]; trivial.
apply (ex2 Adv); [exact adv_ll | apply dmap_ll; exact dkey_ll | apply dmap_ll; exact dkey_ll].
qed.

lemma otp_exp_lb (Adv <: ADV{Sampling}) : islossless Adv.guess => phoare[Otp(Adv).exp : true ==> res] <= ((inv 2%r) + delta_d dkey dunifx).
move => adv_g_ll.
bypr => &m t_{t_}.
have ex_ps : (exists (m0_p : bits, m1_p : bits), m0{m} = m0_p /\ m1{m} = m1_p).
exists m0{m}. by exists m1{m}.
elim ex_ps => m0_p m1_p [m0_eq m1_eq].
rewrite m0_eq m1_eq.
apply (ler_trans ((inv 2%r) * (1%r + delta_d (mkey m0_p) (mkey m1_p))) Pr[Otp(Adv).exp(m0_p, m1_p) @ &m : res] (inv 2%r + delta_d dkey dunifx)).
byphoare (: m0 = m0_p /\ m1 = m1_p ==> res); trivial.
apply (otp_exp_eq Adv m0_p m1_p adv_g_ll).
rewrite mulrDr => //=; rewrite ler_add2l.
apply (ler_trans ((delta_d (mkey m0_p) dunifx + delta_d dunifx (mkey m1_p)) / 2%r)).
rewrite (ler_pmul2r (inv 2%r)); first by rewrite invr_gt0.
apply (ex4_triangle).
rewrite (ex4_symm dunifx) /mkey.
have dmap_uni : forall (ms : bits), dunifx = (dmap dunifx ((+^) ms)).
move => ms.
rewrite dmap_duniform; progress.
by apply (WRing.addrI ms x y).
rewrite /dunifx.
apply eq_duniformP => x; split; progress.
rewrite mapP; exists (ms +^ x); progress; [by exact Support.enumP | by exact inv_xor].
by exact Support.enumP.
rewrite {1}(dmap_uni m0_p). rewrite {2}(dmap_uni m1_p).
rewrite ex3_eq; [by exact inj_xor | by exact dkey_ll | rewrite duniform_ll -size_eq0; smt | trivial].
rewrite ex3_eq; [by exact inj_xor | by exact dkey_ll | rewrite duniform_ll -size_eq0; smt | trivial].
by rewrite mulrDl double_half.
qed.

lemma ex5 (Adv <: ADV{Sampling}) : islossless Adv.guess => phoare[Otp(Adv).main : true ==> res] <= ((inv 2%r) + delta_d dkey dunifx).
proof.
move => adv_ll.
proc.
seq 1 : true 1%r (inv 2%r + delta_d dkey dunifx) 0%r 0%r; trivial.
call (otp_exp_lb Adv); skip; progress.
qed.

print ex5.
