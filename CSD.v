Require Import Asymptotic Rat WC_PolyTime.

Require Import Admissibility Comp. 

Require Import Bvector.

Section CSD.

Variable fcm : FunctionCostModel.
Hypothesis fcm_facts : function_cost_model fcm.

Definition ccm : CompCostModel := comp_cost fcm.

Record Program {A B : nat -> Set} := 
  { dom_eq_dec : forall n, eq_dec (A n)
  ; run :> forall n, A n -> Comp (B n)
  }.

Arguments Program : clear implicits.

Infix "~>" := Program (at level 70).

Require Import DetSem DistRules DistSem.

Record ProgramEquiv {A A' B B'} {f : A ~> B} {g : A' ~> B'} :=
  { codom_eq : forall n, A n = A' n
  ;   dom_eq : forall n, B n = B' n
  ;   run_eq : forall n (x : A n), 
    let x' : A' n := eq_rect (A n) (fun t => t) x _ (codom_eq n) in
     dist_sem_eq 
       (eq_rect _ _ (run f n x) _ (dom_eq n))
       (run g n x')
  }.

Arguments ProgramEquiv {A} {A'} {B} {B'} f g : clear implicits. 

Lemma transport {A A' B B'} :
  (forall n, A n = A' n) -> (forall n, B n = B' n)
  -> A ~> B -> A' ~> B'.
Proof.
intros. constructor.
intros. rewrite <- H. apply (dom_eq_dec X).
intros. rewrite <- H in H1. rewrite <- H0.
apply (run X). assumption.
Defined.

Require Import Morphisms. 


Instance dist_sem_eq_Reflexive : forall A, Reflexive (@dist_sem_eq A).
Proof.
intros. unfold Reflexive, dist_sem_eq. intros.
reflexivity.
Qed.

Instance dist_sem_eq_Symmetric : forall A, Symmetric (@dist_sem_eq A).
Proof.
intros. unfold Symmetric, dist_sem_eq. intros.
symmetry. apply H.
Qed.

Instance dist_sem_eq_Transitive : forall A, Transitive (@dist_sem_eq A).
Proof.
intros. unfold Transitive, dist_sem_eq. intros.
transitivity (evalDist y a). apply H. apply H0.
Qed.

Lemma transport_equiv {A A' B B'} (Aeq : forall n, A n = A' n)
  (Beq : forall n, B n = B' n) (f : A ~> B)
  : ProgramEquiv f (transport Aeq Beq f).
Proof.
refine (
  {| codom_eq := Aeq
   ; dom_eq := Beq
  |}).
intros. simpl. destruct (Beq n). simpl.
destruct (Aeq n). unfold eq_rec_r. simpl.
unfold x'. simpl. reflexivity.
Qed.

Inductive prg_cost {A B} {f : A -> Comp B} {cost : nat} : Prop :=
  Mkcomp_cost : forall c1 c2, fcm _ _ f c1 -> (forall x, ccm _ (f x) c2) -> c1 + c2 <= cost -> prg_cost.

Arguments prg_cost {A} {B} f cost : clear implicits.

Definition prog_cost {A B} (f : forall n, A n -> Comp (B n)) (cost : nat -> nat) : Prop :=
  forall n, prg_cost (f n) (cost n).

Definition comp {B C} (g : B -> C) {A} (f : A -> B) (x : A) : C := g (f x).

Infix "@" := comp (at level 30).

Definition compose {A B C} (f : forall n, A n -> Comp (B n))
  (g : forall n, B n -> Comp (C n)) : forall n : nat, A n -> Comp (C n)
  := fun n x => Bind (f n x) (g n).

Definition composeP {A B C} (f : A ~> B) (g : B ~> C) : A ~> C :=
  {| run := compose f g
   ; dom_eq_dec := dom_eq_dec f
  |}.

Lemma compose_cost : forall A B C (f : forall n, A n -> Comp (B n)) (g : forall n, B n -> Comp (C n)) costf costg,
  prog_cost f costf -> prog_cost g costg
  -> prog_cost (compose f g) (fun n => costf n + costg n).
Proof.
intros. unfold prog_cost in *. 
intros n. specialize (H n). specialize (H0 n).
induction H, H0. econstructor. simpl. instantiate (1 := c1).
replace c1 with (c1 + 0 + 0) by omega.
admit.
intros x. simpl. eapply comp_cost_Bind. simpl.
unfold ccm in *. apply H1. apply H0.
intros. apply H3. eapply Le.le_trans. Focus 2. 
apply Plus.plus_le_compat; eassumption.
omega.
Qed.

Definition prg_id {A} (deceq : forall n, eq_dec (A n)) : A ~> A 
  := {| run := fun n x => Ret (deceq n) x
      ; dom_eq_dec := deceq
     |}.

Inductive PPT {A B} {f : forall n, A n -> Comp (B n)} : Prop :=
  IsPPT : forall cost, prog_cost f cost -> polynomial cost -> PPT.

Arguments PPT {A} {B} f : clear implicits.

Fixpoint repeat_k {A : nat -> Type} (k : nat) (f : forall n, A n -> (A (S n)))
  : forall n, A n -> A (k + n)
  := fun n => match k with
  | 0 => fun x => x
  | S k' => fun x => f _ (repeat_k k' f _ x)
  end. 

Definition lift (p : nat -> nat) {A B : nat -> Set} (f : forall n, A n -> Comp (B n))
  : forall n, A (p n) -> Comp (B (p n)) := fun n => f (p n).

Lemma lift_cost : forall (p : nat -> nat) A B (f : forall n, A n -> Comp (B n)) cost,
  prog_cost f cost -> prog_cost (fun n => f (p n)) (fun n => cost (p n)).
Proof.
unfold prog_cost. intros. apply (H (p n)).
Qed.


Require Import FunctionalExtensionality.
Definition next_lift {A} {r} (k : nat) (f : A ~> A @ plus r) : 
  A @ plus k ~> A @ plus (r + k).
Proof.
pose (
{| run := fun n => run f (k + n)
   ; dom_eq_dec := fun n => dom_eq_dec f (k + n)
  |}
) as f'.
refine (transport _ _ f'); unfold comp; intros.
reflexivity. rewrite Plus.plus_assoc. reflexivity.
Defined.

Definition repeat_k_prg {A : nat -> Set} (k : nat) (f : forall n, A n -> Comp (A (S n)))
  : forall n, A n -> Comp (A (k + S n)).
Proof.
induction k.
- simpl. apply f.
- pose (compose f (lift S IHk)) as f'. intros.
  simpl. rewrite plus_n_Sm.
  apply f'. assumption.
Defined.

Definition repeat_n_prg {A : nat -> Set} (p : nat -> nat) (f : forall n, A n -> Comp (A (S n)))
  (pmono : forall n, n < p n)
  : forall n, A n -> Comp (A (p n)).
Proof.
intros n. unfold comp.
rewrite (Minus.le_plus_minus _ _ (pmono n)).
pose ((repeat_k_prg (p n - S n) f) n) as f'.
rewrite Plus.plus_comm. apply f'.
Defined.

Theorem polynomial_compose : forall f g, polynomial f -> polynomial g
  -> polynomial (fun n => g (f n)).
Proof.
intros. unfold polynomial.
destruct H as (fx & fc1 & fc2 & Pf).
destruct H0 as (gx & gc1 & gc2 & Pg).
(*
exists (gx * fx). do 2 eexists. 
intros n. 
specialize (Pg (f n)). specialize (Pf n).
rewrite Pg.
pose proof (StdNat.expnat_base_le gx Pf).
specialize (H gx _ _ Pf). 

eapply (Pg (f n)).
*)
Admitted.

Theorem repeat_n_admissible : forall (A : nat -> Set) (f : A ~> A @ S)
  (p : nat -> nat) (pmono : forall n, n < p n), polynomial p ->
  PPT f -> PPT (repeat_n_prg p f pmono).
Proof.
intros. induction H0.
apply IsPPT with (fun n => p n * cost (p n)).
admit.
apply polynomial_mult; try assumption.
apply polynomial_compose; assumption.
Admitted.


Lemma PPT_compose : forall {A B C} (f : forall n, A n -> Comp (B n)) (g : forall n, B n -> Comp (C n)),
  PPT f -> PPT g -> PPT (compose f g).
Proof.
intros. destruct H, H0.
econstructor. 
apply compose_cost; eassumption.
apply polynomial_plus; assumption.
Qed.

Require Import DistSem.
Require Import Rat.

Local Open Scope rat.

Definition CSD {A} (mu1 mu2 : Comp A) (test : A -> Comp bool)
  := | Pr [ Bind mu1 test ] - Pr [ Bind mu2 test ] |.

Lemma CSD_self {A} : forall (mu : Comp A) (test : A -> Comp bool),
  CSD mu mu test == 0.
Proof.
intros. unfold CSD.
apply -> ratIdentityIndiscernables.
reflexivity.
Qed.

Lemma CSD_triangle {A} : forall (a b c : Comp A) (test : A -> Comp bool)
 , CSD a c test <= CSD a b test + CSD b c test.
Proof.
intros. apply ratTriangleInequality.
Qed.

Lemma CSD_sym {A} : forall (a b : Comp A) (test : A -> Comp bool),
  CSD a b test == CSD b a test.
Proof.
intros. apply ratDistance_comm.
Qed.
  

Definition PrFamily (A : nat -> Set) := forall n, Comp (A n).

Definition lift_dist {A} (p : nat -> nat) (mu : PrFamily A) : PrFamily (A @ p)
  := fun n => mu (p n).

Definition Distinguisher (A : nat -> Set) := forall n, A n -> Comp ((fun _ => bool) n).

Definition map {A B : nat -> Set} (f : forall n, A n -> Comp (B n)) (mu : PrFamily A) : PrFamily B
  := fun n => Bind (mu n) (f n).

Definition eq_PrFam {A} (x y : PrFamily A) : Prop :=
  forall n, dist_sem_eq (x n) (y n).

Instance eq_PrFam_Equivalence : forall A, Equivalence (@eq_PrFam A).
Proof.
intros. constructor; 
unfold Reflexive, Symmetric, Transitive, eq_PrFam; intros.
reflexivity. symmetry. apply H.
transitivity (y n). apply H. apply H0. 
Qed.

Infix "==" := eq_PrFam : Fam_scope. 
Delimit Scope Fam_scope with Fam.

Theorem map_compose : forall {A B C : nat -> Set} (f : forall n, A n -> Comp (B n)) (g : forall n, B n -> Comp (C n))
  (mu : PrFamily A),
  (map g (map f mu) == map (compose f g) mu)%Fam.
Proof.
intros. unfold eq_PrFam. intros.
unfold map. simpl. apply evalDist_assoc_eq.
Qed.

Definition CSD_fam {A : nat -> Set} (mu1 mu2 : PrFamily A)
  (test : Distinguisher A) (n : nat) : Rat :=
  CSD (mu1 n) (mu2 n) (test n).

Definition CI {A : nat -> Set} (mu1 mu2 : PrFamily A) : Prop :=
  forall test : Distinguisher A, PPT test ->
    negligible (CSD_fam mu1 mu2 test).

Infix "~~" := CI (at level 70).

Definition unlift_distinguisher {p A} 
  (pmono : forall n, (n <= p n)%nat)
  (f : Distinguisher (A @ p))
  : Distinguisher A.
Abort.

Lemma lift_CI {A} (p : nat -> nat) (mu1 mu2 : PrFamily A)
  (pmono : forall n, (n <= p n)%nat)
  : mu1 ~~ mu2 -> lift_dist p mu1 ~~ lift_dist p mu2.
Proof.
unfold CI. intros.
unfold lift_dist.  simpl. unfold CSD_fam.
Admitted.

Lemma negligible_zero : negligible (fun _ => 0).
Proof.
unfold negligible. intros. exists 0%nat.
intros. 
unfold not. intros.
apply leRat_0_eq in H0.
pose proof (StdNat.expnat_pos c H).
refine (@rat_num_nz 1%nat _ _ _).
unfold gt, lt. reflexivity. apply H0.
Qed.

Lemma CI_refl {A} : forall (mu : PrFamily A), mu ~~ mu.
Proof.
unfold CI. intros. eapply negligible_eq. apply negligible_zero. 
intros. simpl. unfold CSD_fam. rewrite CSD_self.
reflexivity.
Qed.

Lemma CI_sym {A} : forall (mu1 mu2 : PrFamily A), mu1 ~~ mu2 -> mu2 ~~ mu1.
Proof.
unfold CI. intros. eapply negligible_eq. apply H. eassumption.
intros. apply CSD_sym.
Qed.

Lemma CI_trans {A} : forall (a b c : PrFamily A), a ~~ b -> b ~~ c -> a ~~ c.
Proof.
unfold CI. intros. eapply negligible_le.
intros. apply (@CSD_triangle _ _ (b n)).
apply negligible_plus. apply H. assumption.
apply H0. assumption.
Qed.

Instance CI_Reflexive : forall A, Reflexive (@CI A).
Proof.
unfold Reflexive. intros. apply CI_refl.
Qed.

Instance CI_Symmetric : forall A, Symmetric (@CI A).
Proof.
unfold Symmetric. intros. apply CI_sym. assumption.
Qed.

Instance CI_Transitive : forall A, Transitive (@CI A).
Proof.
unfold Transitive. intros. eapply CI_trans; eassumption.
Qed.

Instance CI_Equivalence : forall A, Equivalence (@CI A).
Proof.
intros. constructor. apply CI_Reflexive. apply CI_Symmetric.
apply CI_Transitive.
Qed.

Lemma CI_cong {A B} : forall (a b : PrFamily A) (f : forall n, A n -> Comp (B n)),
  PPT f -> a ~~ b -> map f a ~~ map f b.
Proof.
unfold CI. intros.
assert (forall n, CSD_fam (map f a) (map f b) test n == CSD_fam a b (compose f test) n).
intros. unfold CSD_fam, map. simpl. unfold CSD. 
pose proof (DistRules.evalDist_assoc_eq (a n) (f n) (test n) true).
rewrite <- H2. 
pose proof (DistRules.evalDist_assoc_eq (b n) (f n) (test n) true).
rewrite <- H3.
reflexivity.
eapply negligible_eq. Focus 2. intros. rewrite <- H2.
reflexivity.
apply H0.
apply PPT_compose; assumption.
Qed.

Instance Bind_Proper_dse : forall A B, Proper (@dist_sem_eq A ==> eq ==> @dist_sem_eq B) (@Bind B A).
Proof.
unfold Proper, respectful. intros. unfold dist_sem_eq in *.
intros. subst.  simpl.
rewrite (@rel_sumList_compat _ _ (fun b : A => evalDist y b * evalDist (y0 b) a) _ eqRat).
apply Fold.sumList_subset.
apply comp_eq_dec. assumption. apply support_NoDup. apply support_NoDup.
intros a0. rewrite !getSupport_In_evalDist. intros.
rewrite <- (H a0). assumption.
intros a0. rewrite !getSupport_not_In_evalDist. rewrite (H a0).
intros.  rewrite H0. apply ratMult_0_l. apply eqRat_RatRel.
intros a0. rewrite !getSupport_In_evalDist. rewrite !(H a0).
intros. reflexivity.
Qed.

Theorem eq_dec_refl {A} (de : eq_dec A) (x : A) {B} (t f : B) : 
  (if de x x then t else f) = t.
Proof.
destruct (de x x). reflexivity. congruence.
Qed.

Inductive permutation {A B} {f : A -> B} :=
  { f_inv : B -> A
  ; to_from : forall a, f_inv (f a) = a
  ; from_to : forall b, f (f_inv b) = b
  }.

Arguments permutation {A} {B} f : clear implicits.

Definition map_prob {A B : Set} (de : eq_dec B) (f : A -> B) (mu : Comp A) : Comp B
  := Bind mu (fun x => Ret de (f x)).

Definition perm_uniform {A B : Set} (f : A -> B)
  (permf : permutation f)
  (de : eq_dec B)
  (mu : Comp A)
  (prob : Rat)
  (prob_nz : ~ prob == 0)
  (mu_uniform : forall x, evalDist mu x == prob)
  : forall x, evalDist (map_prob de f mu) x == prob.
Proof.
intros. simpl.
rewrite (@Fold.sumList_exactly_one _ (f_inv permf x)).
rewrite from_to, eq_dec_refl, mu_uniform.
apply ratMult_1_r.
apply support_NoDup.
apply getSupport_In_evalDist. rewrite mu_uniform.
assumption.
intros. apply ratMult_0. right.
destruct (de (f b) x). unfold not in H0. apply False_rect.
apply H0. rewrite <- (to_from permf). rewrite e. reflexivity.
reflexivity.
Qed.

Definition perm_uniform_Bvector : forall n
  (f : Bvector n -> Bvector n),
  permutation f -> 
  dist_sem_eq (@Rnd n) (map_prob (@Bvector_eq_dec n) f (@Rnd n)).
Proof.
intros.
unfold dist_sem_eq.
intros. symmetry. apply perm_uniform. assumption. unfold evalDist.
unfold eqRat, beqRat. simpl. congruence.
intros. apply uniformity.
Qed.

Instance evalDist_Proper : forall A, Proper (@dist_sem_eq A ==> eq ==> eqRat) (@evalDist A).
Proof.
unfold Proper, respectful. intros. subst.
apply H.
Qed.

Instance CSD_Proper : forall A, Proper (@dist_sem_eq A ==> @dist_sem_eq A ==> eq ==> eqRat) (@CSD A).
Proof.
unfold Proper, respectful. intros. subst.
unfold CSD. rewrite H, H0. reflexivity.
Qed.

Instance CSD_fam_Proper : forall A, Proper (eq_PrFam ==> eq_PrFam ==> eq ==> pointwise_relation _ eqRat) (@CSD_fam A).
Proof.
intros. unfold Proper, respectful, pointwise_relation.
intros. unfold CSD_fam. subst. unfold eq_PrFam in *.
rewrite (H a), (H0 a). reflexivity.
Qed.

Instance negligible_Proper : Proper (pointwise_relation _ eqRat ==> iff) negligible.
Proof.
unfold Proper, respectful, pointwise_relation.
intros. split; intros; eapply negligible_eq; eauto.
intros. symmetry. apply H.
Qed.

Instance CI_Proper : forall A, Proper (eq_PrFam ==> eq_PrFam ==> iff) (@CI A).
Proof.
unfold Proper, respectful, CI. intros. split; intros.
- rewrite <- H, <- H0. apply H1; assumption.
- rewrite H, H0. apply H1; assumption.
Qed.

Definition BPrFamily (length : nat -> nat) := forall n, Comp (Bvector (length n)).

Definition uniform {l} : BPrFamily l := fun n => Rnd (l n).

Lemma uniform_lift_id {l} : @uniform l = lift_dist l (@uniform id).
Proof. 
reflexivity.
Qed.

Definition BComp (length : nat -> nat) := forall n, Bvector n -> Comp (Bvector (length n)).

Definition Bcompose {l1 l2} (f : BComp l1) (g : BComp l2)
  : BComp (fun n => l2 (l1 n))
  := fun n x => Bind (f n x) (g (l1 n)).

Definition toProg {l} (f : BComp l) : Bvector ~> Bvector @ l.
Proof.
refine ({| run := f |}).
intros. unfold eq_dec. apply Bvector_eq_dec.
Defined.

Definition Bmap {lf lmu} (f : BComp lf) (mu : BPrFamily lmu)
  : BPrFamily (fun n => lf (lmu n))
  := fun n => Bind (mu n) (f (lmu n)).

Lemma Bmap_Bcompose : forall l l1 l2 (f : BComp l1) (g : BComp l2),
  forall (mu : BPrFamily l), (Bmap (Bcompose f g) mu == Bmap g (Bmap f mu))%Fam.
Proof.
intros.
unfold Bmap, Bcompose, eq_PrFam.
intros. symmetry. apply evalDist_assoc_eq.
Qed.

Definition Bdeterministic {l} (f : forall n, Bvector n -> Bvector (l n))
  : BComp l := fun n x => Ret (@Bvector_eq_dec (l n)) (f n x).

Definition map_det {l lf} (f : forall n, Bvector n -> Bvector (lf n))
  (mu : BPrFamily l) : BPrFamily (fun n => lf (l n))
  := fun n => map_prob (@Bvector_eq_dec (lf (l n))) (f (l n)) (mu n).


Definition Bpermutation (f : forall n, Bvector n -> Bvector n) 
  (permf : forall n, permutation (f n))
  (l : nat -> nat)
  : (Bmap (Bdeterministic f) (@uniform l) == uniform)%Fam.
Proof.
unfold eq_PrFam. intros n.
unfold Bmap, Bdeterministic, uniform.
pose proof perm_uniform_Bvector as H.
unfold map_prob in H. symmetry. apply H.
apply permf.
Qed.

Lemma Bmap_map {l lf} : forall (f : BComp lf) (mu : BPrFamily l),
  Bmap f mu = map (lift l f) mu.
Proof.
intros. unfold Bmap, map. simpl. reflexivity.
Qed.

Record PRG {l : nat -> nat} {G : BComp l} :=
  { length_stretches : forall n, n < l n
  ; looks_random : Bmap G (@uniform id) ~~ uniform
  ; is_PPT : PPT G
  }.

Arguments PRG {l} G : clear implicits.

Lemma map_lift : forall {A B : nat -> Set} (f : forall n, A n -> Comp (B n)) p mu, map (lift p f) (lift_dist p mu)
  = lift_dist p (map f mu).
Proof.
intros. unfold map, lift_dist. simpl. reflexivity.
Qed.

Lemma looks_random_lift {l G} : @PRG l G
  -> forall (p : nat -> nat) (pmono : forall n, (n <= p n)%nat)
  , Bmap G (@uniform p) ~~ uniform.
Proof.
intros. rewrite (Bmap_map G uniform).
rewrite (@uniform_lift_id p).
rewrite (@uniform_lift_id (fun n => l (p n))).
rewrite (map_lift G p). 
pose (mu := lift_dist p (lift_dist l (@uniform id))).
unfold comp, id in mu.
transitivity mu. unfold mu.
pose proof (@lift_CI (fun x => Bvector (l x)) p
  (map (toProg G) uniform)
  (lift_dist l (@uniform id))).
apply H0. assumption. clear H0. rewrite <- uniform_lift_id.
apply (looks_random H). unfold mu. reflexivity.
Qed.

(** Problem Set 2, Question 4, part 2 *)

(** G is a pseudorandom generator *)
Variable len : nat -> nat.
Variable G : BComp len.
Hypothesis G_is_PRG : PRG G.

Axiom output_bounds_cost : forall A (len cost : nat -> nat)
  (f : forall n, A n -> Comp (Bvector (len n))),
  prog_cost f cost -> (forall n, (len n <= cost n)%nat).

Theorem polynomial_le : forall (f g : nat -> nat),
  (forall n, (f n <= g n)%nat) -> polynomial g -> polynomial f.
Proof.
intros. unfold polynomial in *.
destruct H0 as (x & c1 & c2 & bound).
exists x. exists c1. exists c2. intros. rewrite H. apply bound.
Qed.

Theorem PPT_bounds_len : forall A (len : nat -> nat)
  (f : forall n, A n -> Comp (Bvector (len n))),
  PPT f -> polynomial len.
Proof.
intros. induction H. eapply polynomial_le.
eapply output_bounds_cost. eassumption.
assumption.
Qed.

Lemma lift_PPT : forall (p : nat -> nat) {A B}
  (f : forall n, A n -> Comp (B n)),
  polynomial p ->
  PPT f -> PPT (fun n => f (p n)).
Proof.
intros. induction H0. econstructor.
apply lift_cost. eassumption.
apply polynomial_compose; assumption.
Qed.

Lemma G_len_PPT : PPT (fun n : nat => G (len n)).
Proof.
apply (@lift_PPT len _ _ G).
eapply PPT_bounds_len. apply (is_PPT G_is_PRG).
apply (is_PPT G_is_PRG).
Qed.

Theorem partA : PRG (Bcompose G G).
Proof.
constructor.
- intros. pose proof (length_stretches G_is_PRG).
  eapply Lt.lt_trans. apply H. apply H.
- rewrite Bmap_Bcompose. 
  transitivity (Bmap G (@uniform len)).
  rewrite !Bmap_map. apply CI_cong. simpl. 
  apply G_len_PPT.
  apply (looks_random G_is_PRG).
  apply looks_random_lift. assumption. unfold id.
  intros. apply Lt.lt_le_weak. apply (length_stretches G_is_PRG).
- unfold Bcompose. simpl.
  apply PPT_compose.  apply (is_PPT G_is_PRG).
  apply G_len_PPT.
Qed.

Variable perm : forall n, Bvector n -> Bvector n.
Hypothesis perm_is_permutation : forall n, permutation (perm n).

Definition h : BComp id := Bdeterministic perm.

Hypothesis h_efficient : PPT h.

Theorem partC : PRG (Bcompose G h).
Proof.
constructor.
- intros. unfold id. apply (length_stretches G_is_PRG).
- rewrite Bmap_Bcompose. 
  transitivity (Bmap h (@uniform len)).
  apply CI_cong. apply lift_PPT. eapply PPT_bounds_len.
  eapply (is_PPT G_is_PRG). apply h_efficient.
  apply (looks_random G_is_PRG).
  unfold h.
  eapply CI_Proper. apply Bpermutation. apply perm_is_permutation.
  reflexivity. reflexivity.
- apply PPT_compose. apply (is_PPT G_is_PRG). 
  apply lift_PPT. eapply PPT_bounds_len. apply (is_PPT G_is_PRG). 
  assumption.
Qed.

Theorem partD : PRG (Bcompose h G).
Proof.
constructor.
- intros. unfold id. apply (length_stretches G_is_PRG).
- rewrite Bmap_Bcompose.
  transitivity (Bmap G (@uniform id)).
  apply CI_cong. apply (is_PPT G_is_PRG).
  unfold h. rewrite Bpermutation. reflexivity.
  apply perm_is_permutation. apply (looks_random G_is_PRG).
- apply PPT_compose. apply h_efficient.
  apply (is_PPT G_is_PRG).
Qed.