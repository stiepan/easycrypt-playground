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


lemma f_inq : forall (f : X -> X), true => forall (da : X distr), is_lossless da => forall (db : X distr), is_lossless db => delta_d (dmap da f) (dmap db f) <= delta_d da db.
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
smt.
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


lemma mul_sides : forall (x, y, z : real), x <> 0%r => x * y = x * z <=> y = z.
proof.
smt.
qed.


lemma f_eq : forall (f : X -> X), injective f => forall (da : X distr), is_lossless da => forall (db : X distr), is_lossless db => delta_d (dmap da f) (dmap db f) = delta_d da db.
proof.
move => f inj_f da da_ll db db_ll.
rewrite /delta_d.
rewrite mul_sides. rewrite invr_eq0 => //.
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


(* just to play with cloning *)
lemma bits_f_inq : forall (f : bits -> bits), true => forall (da : bits distr), is_lossless da => forall (db : bits distr), is_lossless db => Sbits.delta_d (dmap da f) (dmap db f) <= Sbits.delta_d da db.
by exact Sbits.f_inq.
qed.


module type ADV = {
  proc guess(x : bits) : bool
}.

section.

op da : bits distr.

axiom da_ll : is_lossless da.

op db : bits distr.

axiom db_ll : is_lossless db.


module Exp (Adv : ADV) = {

  var b, ba : bool

  proc main() : bool = {
    var d : bits distr;
    var x : bits;
    b <$ {0,1};
    d <- if !b then da else db;
    x <$ d;
    ba <- Adv.guess(x);
    return ba;
  }
}.


declare module Adv : ADV{Exp}.

axiom Adv_ll : islossless Adv.guess.


lemma disting0 &m: (phoare [Exp(Adv).main : true ==> Exp.ba = Exp.b] = ((inv 2%r * big predT (fun x => Pr[Adv.guess(x) @ &m : false] * mu1 da x) Support.enum) + (inv 2%r * big predT (fun x => Pr[Adv.guess(x) @ &m : true] * mu1 db x) Support.enum))).
proof.
proc.
phoare split (
  inv 2%r * big predT (fun (x0 : bits) => Pr[Adv.guess(x0) @ &m : false] * mu1 da x0) Support.enum
) (
  inv 2%r * big predT (fun (x0 : bits) => Pr[Adv.guess(x0) @ &m : true] * mu1 db x0) Support.enum
) : (!Exp.b) => //.
(*seq 2 : (!Exp.b /\ d = da) (inv 2%r) (big predT (fun (x0 : bits) => Pr[Adv.guess(x0) @ &m : false] * mu1 da x0) Support.enum) (inv 2%r) 0%r.*)
admit. admit.
qed.



lemma disting &m : Pr[Exp(Adv).main() @ &m : res] <= inv 2%r * (1%r + delta_d da db).
proof.
byphoare.
proc.
(*call (_ : b = b ==> b = b').
seq 1 : ((b \in {0,1}) /\ mu1 dbool b = inv 2%r).
rnd. skip. auto.
rnd. skip.
call (_ : true ==> true).
seq 3 : true.
call (_ : true ==> true).
apply Adv_ll.
seq 1 : true.
rnd.
skip. auto.*)
admit. admit. admit.
qed.
end section.

