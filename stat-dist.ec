require import Bool AllCore List Finite Discrete Distr.
require import StdRing StdOrder StdBigop RealLub RealSeq RealSeries Bigalg.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import Ring.IntID IntOrder RField RealOrder Number.

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
rewrite -subr_eq0.
rewrite sumrN. simplify.
have lel : (fun x => mu1 da x <= mu1 db x) = predC (fun x => mu1 da x > mu1 db x).
apply fun_ext. rewrite /(==).
move => ?. rewrite /predC. rewrite ltr_def.
rewrite negb_and. simplify. smt.
rewrite lel.
have lol : (fun (x : X) => - (mu1 db x - mu1 da x)) = (fun (x : X) => mu1 da x - mu1 db x).
apply fun_ext. rewrite /(==). move => ?.
rewrite opprB. trivial.
rewrite lol.
rewrite -bigEM.
rewrite big_split.
rewrite -sumrN.
have xd: (fun (i : X) => mu1 da i) = (fun (i : X) => mass da i).
apply fun_ext. rewrite /(==). move => ?.
rewrite massE. trivial.
have dd : Support.enum = undup (Support.enum).
rewrite undup_id.
apply Support.enum_uniq. trivial. rewrite dd.
rewrite -(mu_mem da Support.enum).
rewrite -(mu_mem db Support.enum).
have xdd: mem Support.enum = predT.
rewrite /predT. apply fun_ext. rewrite /(==). move => ?. rewrite (Support.enumP x). trivial.
rewrite xdd.
rewrite is_losslessP. assumption.
rewrite is_losslessP. assumption.
auto.
qed.

lemma delta_d_alt (da : X distr, db : X distr) : is_lossless da => is_lossless db => delta_d da db = big (fun x => mu1 da x > mu1 db x) (fun x => mu1 da x - mu1 db x) (Support.enum).
proof.
move => ? ?.
rewrite /delta_d.
rewrite {1} (bigEM (fun (x : X) => mu1 da x > mu1 db x)).
rewrite {1} big_mkcond. simplify.
have lel : (fun (i : X) =>
      if mu1 db i < mu1 da i then `|mu1 da i - mu1 db i| else 0%r) = (fun (i : X) => if mu1 db i < mu1 da i then mu1 da i - mu1 db i else 0%r).
apply fun_ext. rewrite /(==). move => ?.
case ( mu1 db x < mu1 da x).
move => ?. smt.
auto. rewrite lel. rewrite - {1} big_mkcond.
have ror : (fun x => mu1 db x >= mu1 da x) = predC (fun x => mu1 db x < mu1 da x).
apply fun_ext. rewrite /(==).
move => ?. rewrite /predC. smt.
rewrite -ror.
have dd : (big (fun (x : X) => mu1 da x <= mu1 db x)
   (fun (x : X) => `|mu1 da x - mu1 db x|) Support.enum) = (big (fun (x : X) => mu1 da x <= mu1 db x)
   (fun (x : X) => mu1 db x - mu1 da x) Support.enum).
rewrite big_mkcond. simplify.
have ddd : (fun (i : X) =>
      if mu1 da i <= mu1 db i then `|mu1 da i - mu1 db i| else 0%r) = (fun (i : X) => if mu1 da i <= mu1 db i then mu1 db i - mu1 da i else 0%r).
apply fun_ext. rewrite /(==). move => ?.
case ( mu1 da x <= mu1 db x).
move => ?. rewrite -normrN. smt.
auto.
rewrite ddd. rewrite -big_mkcond. reflexivity.
rewrite dd.
rewrite big_sym => //.
smt.
qed.

(*op compose (f : X -> X) (da : X distr) : X distr.

axiom compose_mu1 (f : X -> X) (da : X distr) (y : X) : mu1 (compose f da) y = big predT (fun x' => if f x' = y then mu1 da x' else 0%r) Support.enum.

lemma compose_ll (f : X -> X) (da : X distr) : is_lossless da => compose f *)


lemma f_inq : forall (f : X -> X), true => forall (da : X distr), is_lossless da => forall (db : X distr), is_lossless db => delta_d (dmap da f) (dmap db f) <= delta_d da db.
move => ? ? ? ? ? ?.
rewrite /delta_d.
rewrite ler_pmul2l. apply invr_gt0. auto.
have lol : (fun (x : X) => `|mu1 (dmap da f) x - mu1 (dmap db f) x|) = (fun (x : X) => `|big predT (fun (x0 : X) => if f x0 = x then mu1 da x0 else 0%r) Support.enum - big predT (fun (x0 : X) => if f x0 = x then mu1 db x0 else 0%r) Support.enum|).
apply fun_ext. rewrite /(==). move => ?.
rewrite !dmap1E. rewrite !/(\o). rewrite !muE. simplify.
rewrite {1 2}/pred1.

rewrite (sumE_fin (fun (x0 : X) => if f x0 = x then mass da x0 else 0%r) (Support.enum)).
apply Support.enum_uniq. simplify.
move => ? ?. apply (Support.enumP x0).
rewrite (sumE_fin (fun (x0 : X) => if f x0 = x then mass db x0 else 0%r) (Support.enum)).
apply Support.enum_uniq. simplify.
move => ? ?. apply (Support.enumP x0).

have omg : forall (d : X distr), true => (fun (x0 : X) => if f x0 = x then mass d x0 else 0%r) = (fun (x0 : X) => if f x0 = x then mu1 d x0 else 0%r).
move => ? _.
apply fun_ext. rewrite /(==). move => ?.
rewrite massE. trivial.
rewrite !omg => //.
rewrite lol.

have dd : (fun (x : X) =>
     `|big predT (fun (x0 : X) => if f x0 = x then mu1 da x0 else 0%r)
         Support.enum -
       big predT (fun (x0 : X) => if f x0 = x then mu1 db x0 else 0%r)
         Support.enum|) = (fun (x : X) =>
     `|big (fun (x0 : X) => f x0 = x) (fun (x0 : X) => mu1 da x0 - mu1 db x0)
         Support.enum|).
apply fun_ext. rewrite /(==). move => ?.
rewrite sumrN. simplify.
have meh : (fun (x0 : X) => - (if f x0 = x then mu1 db x0 else 0%r)) = (fun (x0 : X) => (if f x0 = x then - (mu1 db x0) else 0%r)).
apply fun_ext. rewrite /(==). move => ?.
by case (f x0 = x).
rewrite meh.
rewrite -big_mkcond.
rewrite -big_mkcond.
rewrite -big_split; simplify. auto.
rewrite dd.

have mhm : big predT (fun (x : X) => 
    `|big (fun (x0 : X) => f x0 = x) (fun (x0 : X) => mu1 da x0 - mu1 db x0) Support.enum|) Support.enum <= big predT (fun (x : X) =>
     big (fun (x0 : X) => f x0 = x) (fun (x0 : X) => `|mu1 da x0 - mu1 db x0|)
         Support.enum) Support.enum.
apply ler_sum.
move => ? ?.
simplify.
apply big_normr.


have ror : (big predT (fun (x : X) =>
     big (fun (x0 : X) => f x0 = x) (fun (x0 : X) => `|mu1 da x0 - mu1 db x0|)
         Support.enum) Support.enum) = (big predT (fun (x : X) => `|mu1 da x - mu1 db x|) Support.enum).
rewrite (partition_big f predT predT (fun (x0 : X) => `|mu1 da x0 - mu1 db x0|) (Support.enum) (Support.enum)).
by apply Support.enum_uniq.
move => ? ? ?.
split.
apply Support.enumP.
rewrite /predT => //.
trivial.
rewrite -ror.
by apply mhm.
qed.

