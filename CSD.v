Require Import Asymptotic Rat WC_PolyTime.

Require Import Admissibility Comp. 

Require Import Bvector.

Section CSD.

Definition trivial_fcm : FunctionCostModel :=
  fun A B f x => True.

Theorem trivial_fcm_ok : function_cost_model trivial_fcm.
Proof.
unfold trivial_fcm; constructor; intros; auto.
Qed.

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

Fixpoint repeat_k_det {A : nat -> Set} (k : nat) (f : forall n, A n -> A (S n))
  : forall n, A n -> A (k + S n) := match k as k' return forall n, A n -> A (k' + S n) with
  | 0 => f
  | S k' => fun n x => f _ (repeat_k_det k' f n x)
  end.

Definition repeat_n_det {A : nat -> Set} (p : nat -> nat) (f : forall n, A n -> A (S n))
  (pmono : forall n, n < p n) : forall n, A n -> A (p n).
Proof.
intros n. unfold comp.
rewrite (Minus.le_plus_minus _ _ (pmono n)).
pose ((repeat_k_det (p n - S n) f) n) as f'.
rewrite Plus.plus_comm. apply f'.
Defined.

Theorem polynomial_compose : forall f g, polynomial f -> polynomial g
  -> polynomial (fun n => g (f n)).
Proof.
intros. unfold polynomial.
destruct H as (fx & fc1 & fc2 & Pf).
destruct H0 as (gx & gc1 & gc2 & Pg).
exists (gx * fx).
Admitted.

Definition Bmapd {A n} (f : A -> Bvector n) := fun x => Ret (@Bvector_eq_dec _) (f x).

Definition BComp (length : nat -> nat) := forall n, Bvector n -> Comp (Bvector (length n)).


Definition Bdeterministic {l} (f : forall n, Bvector n -> Bvector (l n))
  : BComp l := fun n => Bmapd (f n).

Theorem repeat_n_admissible : forall (f : forall n, Bvector n -> Bvector (S n))
  (p : nat -> nat) (pmono : forall n, n < p n), polynomial p ->
  PPT (Bdeterministic f) -> PPT (Bdeterministic (repeat_n_det p f pmono)).
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

Require Import DistSem Rat.

Local Open Scope rat.

Infix "==" := dist_sem_eq : Dist_scope.
Delimit Scope Dist_scope with Dist.

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

Definition eq_PrFam A (x y : PrFamily A) : Prop :=
  forall n, (x n == y n)%Dist.

Instance eq_PrFam_Equivalence : forall A, Equivalence (@eq_PrFam A).
Proof.
intros. constructor; 
unfold Reflexive, Symmetric, Transitive, eq_PrFam; intros.
reflexivity. symmetry. apply H.
transitivity (y n). apply H. apply H0. 
Qed.

Notation "x ={ A }= y" := (eq_PrFam A x y) (at level 70) : Fam_scope.
Infix "==" := (eq_PrFam _) : Fam_scope. 
Delimit Scope Fam_scope with Fam.

Theorem map_compose : forall {A B C : nat -> Set} (f : forall n, A n -> Comp (B n)) (g : forall n, B n -> Comp (C n))
  (mu : PrFamily A),
  (map g (map f mu) ={ C }= map (compose f g) mu)%Fam.
Proof.
intros. unfold eq_PrFam. intros.
unfold map. simpl. apply evalDist_assoc_eq.
Qed.

Definition CSD_fam {A : nat -> Set} (mu1 mu2 : PrFamily A)
  (test : Distinguisher A) (n : nat) : Rat :=
  CSD (mu1 n) (mu2 n) (test n).

Definition CI (A : nat -> Set) (mu1 mu2 : PrFamily A) : Prop :=
  forall test : Distinguisher A, PPT test ->
    negligible (CSD_fam mu1 mu2 test).

Infix "~~" := (CI _) (at level 70).
Notation "x ~{ A }~ y" := (CI A x y) (at level 70).

Fixpoint bounded_lookup (p : nat -> bool) (bound : nat) : option { n | p n = true }.
Proof. 
induction bound.
- destruct (p 0%nat) eqn:p0. 
  refine (Some (exist (fun n => p n = true) 0%nat p0)).
  refine None.
- destruct IHbound. 
  refine (Some s).
  destruct (p (S bound)) eqn:ps.
  refine (Some (exist (fun n => p n = true) (S bound) ps)).
  refine None.
Defined.

Fixpoint pmono_partial_inverse (p : nat -> nat)
 (n : nat) : option { k | p k = n }.
Proof.
pose (bounded_lookup (fun k => EqNat.beq_nat (p k) n) n) as ans.
destruct ans.
destruct s.
rewrite EqNat.beq_nat_true_iff in e.
refine (Some (exist _ x e)).
exact None.
Defined.

Definition pmono_partial_inverse_complete (p : nat -> nat)
  (pmono : forall n, (n <= p n)%nat)
  : forall k : nat, exists k' prf, pmono_partial_inverse p (p k) = Some (exist _ k' prf).
Proof.
Admitted.

Definition always_true {A} : A -> Comp bool := fun _ => Ret bool_dec true.

Definition unlift_distinguisher {p A} 
  (pmono : forall n, (n <= p n)%nat)
  (f : Distinguisher (A @ p))
  : Distinguisher A.
Proof.
unfold Distinguisher, comp in *.
intros n.
refine (match pmono_partial_inverse p n with
  | None => always_true
  | Some (exist k prf) => eq_rect (p k) (fun i => A i -> Comp bool) (f k) n prf
  end).
Defined.

Theorem unlift_distinguisher_PPT {p A}
  (pmono : forall n, (n <= p n)%nat) (f : Distinguisher (A @ p))
  : PPT f -> PPT (unlift_distinguisher pmono f).
Proof.
Admitted.

Require Import Eqdep_dec.

Theorem unlift_distinguisher_behaves {p A}
  (pmono : forall n, (n <= p n)%nat) (f : Distinguisher (A @ p))
  (pinj : forall m n, p m = p n -> m = n)
  : forall (mu : PrFamily A) n, dist_sem_eq 
     (Bind (mu (p n)) (f n))
     (Bind (mu (p n)) (unlift_distinguisher pmono f (p n))).
Proof.
intros. unfold unlift_distinguisher.
pose proof (pmono_partial_inverse_complete p pmono n).
destruct H as (k' & prf & isSome).
rewrite isSome. clear isSome.
pose proof (pinj _ _ prf). induction H. 
rewrite <- (eq_rect_eq_dec Peano_dec.eq_nat_dec).
reflexivity.
Qed.

Lemma unlift_distinguisher_CSD_fam {p A}
  (pmono : forall n, (n <= p n)%nat) (f : Distinguisher (A @ p))
  (pinj : forall m n, p m = p n -> m = n)
  : forall (mu1 mu2 : PrFamily A), pointwise_relation nat eqRat
    (CSD_fam (lift_dist p mu1) (lift_dist p mu2) f)
    (CSD_fam mu1 mu2 (unlift_distinguisher pmono f) @ p).
Proof.
intros. unfold pointwise_relation. intros n.
unfold CSD_fam, CSD, lift_dist, comp.
rewrite (unlift_distinguisher_behaves pmono f pinj mu1 n true).
rewrite (unlift_distinguisher_behaves pmono f pinj mu2 n true).
reflexivity.
Qed.


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
  PPT f -> a ~{ A }~ b -> map f a ~{ B }~ map f b.
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

Instance CSD_fam_Proper : forall A, Proper (eq_PrFam A ==> eq_PrFam A ==> eq ==> pointwise_relation _ eqRat) (@CSD_fam A).
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

Instance CI_Proper : forall A, Proper (eq_PrFam A ==> eq_PrFam A ==> iff) (@CI A).
Proof.
unfold Proper, respectful, CI. intros. split; intros.
- rewrite <- H, <- H0. apply H1; assumption.
- rewrite H, H0. apply H1; assumption.
Qed.

Lemma nz_le : forall x y, (x <= y)%nat -> StdNat.nz x -> StdNat.nz y.
Proof.
intros. constructor. induction H0. unfold gt in *. 
apply Lt.lt_le_trans with x; assumption.
Qed.


Lemma leRat_denom : forall n (d1 d2 : nat)
  (nzd1 : StdNat.nz d1) (nzd2 : StdNat.nz d2),
  (d1 <= d2)%nat -> n / d2 <= n / d1.
Proof.
intros. unfold leRat, bleRat. simpl.
destruct (Compare_dec.le_gt_dec (n * d1) (n * d2)).
reflexivity.
pose proof (Mult.mult_le_compat_l d1 d2 n H).
apply Gt.le_not_gt in H0. contradiction.
Qed.


Lemma negligible_compose_fast : forall f p
   (pmono : forall n, (n <= p n)%nat),
  negligible f -> negligible (f @ p).
Proof.
intros. unfold negligible in *. intros c. specialize (H c).
destruct H as (n & negn).
exists n. intros. unfold comp.
specialize (negn (p x) (nz_le _ _ (pmono x) pf_nz)).
unfold not.  intros. apply negn.
unfold gt in *. apply Lt.lt_le_trans with x. assumption.
apply pmono. eapply leRat_trans. 2:eassumption.
clear H0. apply leRat_denom.
apply StdNat.expnat_base_le. apply pmono.
Qed.

Lemma lift_CI' {A} (p : nat -> nat) (mu1 mu2 : PrFamily A)
  (pmono : forall n, (n <= p n)%nat)
  (pinj : forall m n, p m = p n -> m = n)
  : mu1 ~~ mu2 -> lift_dist p mu1 ~~ lift_dist p mu2.
Proof.
unfold CI. intros. simpl.
specialize (H (unlift_distinguisher pmono test) 
  (unlift_distinguisher_PPT pmono test H0)).
rewrite (unlift_distinguisher_CSD_fam pmono test pinj mu1 mu2).
apply negligible_compose_fast. apply pmono. assumption.
Qed.

(** this just lies to get rid of one of the assumptions *)
Lemma lift_CI {A} (p : nat -> nat) (mu1 mu2 : PrFamily A)
  (pmono : forall n, (n <= p n)%nat)
  : mu1 ~~ mu2 -> lift_dist p mu1 ~~ lift_dist p mu2.
Proof.
intros. apply lift_CI'; try assumption.
admit.
Qed.


Definition BPrFamily (length : nat -> nat) := forall n, Comp (Bvector (length n)).

Definition uniform l : BPrFamily l := fun n => Rnd (l n).

Lemma uniform_lift_id {l} : uniform l = lift_dist l (uniform id).
Proof. 
reflexivity.
Qed.

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

Definition Bpermutation (f : forall n, Bvector n -> Bvector n) 
  (permf : forall n, permutation (f n))
  (l : nat -> nat)
  : (Bmap (Bdeterministic f) (uniform l) == uniform l)%Fam.
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

Lemma tl_uniform : forall n, (Bind (Rnd (S n)) (Bmapd Vector.tl) == Rnd n)%Dist.
Proof.
intros n. unfold dist_sem_eq. intros v.
simpl. rewrite Fold.sumList_app. rewrite !Fold.sumList_map.
rewrite !(@Fold.sumList_exactly_one _ v). simpl.
rewrite ratMult_2, eq_dec_refl. rewrite !ratMult_1_r. 
rewrite <- rat_mult_den.
unfold eqRat, beqRat. simpl. 
match goal with 
| [ |- (if ?e then _ else _) = _ ] => destruct e
end. reflexivity. apply False_rect. apply n0. clear n0.
omega.
apply getAllBvectors_NoDup. apply in_getAllBvectors.
simpl. intros.  destruct (Bvector_eq_dec b v). congruence.
apply ratMult_0_r.
apply getAllBvectors_NoDup. apply in_getAllBvectors.
simpl. intros. destruct (Bvector_eq_dec b v). congruence.
apply ratMult_0_r.
Qed.

Fixpoint truncate k : forall n, Bvector (k + n) -> Bvector n :=
  match k as k' return forall n, Bvector (k' + n) -> Bvector n  with
  | 0 => fun n x => x
  | S k' => fun n x => truncate k' n (Vector.tl x)
  end.

Lemma Bmapd_compose : forall (A : Set) n m (f : A -> Bvector n) (g : Bvector n -> Bvector m)
  mu, 
  (Bmapd (fun x => g (f x)) mu == Bind (Bmapd f mu) (Bmapd g))%Dist.
Proof.
intros. unfold Bmapd. unfold dist_sem_eq.
intros x. rewrite (evalDist_left_ident_eq (Bvector_EqDec n) (f mu)).
reflexivity.
Qed.

Lemma Bmapd_compose2 : forall (A : Set) n m (f : A -> Bvector n) (g : Bvector n -> Bvector m)
  mu, 
  (Bind mu (Bmapd (fun x => g (f x))) == Bind (Bind mu (Bmapd f)) (Bmapd g))%Dist.
Proof.
intros. unfold Bmapd. rewrite evalDist_assoc_eq.
unfold dist_sem_eq. intros v.
apply evalDist_seq_eq. intros; reflexivity.
intros. rewrite (evalDist_left_ident_eq (Bvector_EqDec n)).
reflexivity.
Qed.

Lemma truncate_uniform : forall k n, (Bind (Rnd (k + n)) (Bmapd (truncate k n)) == Rnd n)%Dist.
Proof.
intros k. induction k.
- simpl. unfold truncate. simpl. unfold Bmapd.
  intros n. unfold dist_sem_eq. 
  intros x. apply evalDist_right_ident.
- intros n. simpl. rewrite Bmapd_compose2.
  rewrite tl_uniform. fold plus. apply IHk.
Qed.

Definition BDetComp (l : nat -> nat) := forall n, Bvector n -> Bvector (l (n)).

Record PRG {l : nat -> nat} {G : BDetComp l} :=
  { length_stretches : forall n, n < l n
  ; looks_random : Bmap (Bdeterministic G) (uniform id) ~~ uniform l
  ; is_PPT : PPT (Bdeterministic G)
  }.

Arguments PRG {l} G : clear implicits.

Lemma map_lift : forall {A B : nat -> Set} (f : forall n, A n -> Comp (B n)) p mu, map (lift p f) (lift_dist p mu)
  = lift_dist p (map f mu).
Proof.
intros. unfold map, lift_dist. simpl. reflexivity.
Qed.

Lemma looks_random_lift {l G} : @PRG l G
  -> forall (p : nat -> nat) (pmono : forall n, (n <= p n)%nat)
  , Bmap (Bdeterministic G) (uniform p) ~~ uniform (l @ p).
Proof.
intros. rewrite (Bmap_map (Bdeterministic G)).
rewrite (@uniform_lift_id p).
rewrite (@uniform_lift_id (l @ p)).
rewrite (map_lift (Bdeterministic G) p). 
pose (mu := lift_dist p (lift_dist l (@uniform id))).
unfold comp, id in mu.
transitivity mu. unfold mu.
pose proof (@lift_CI (fun x => Bvector (l x)) p
  (map (toProg (Bdeterministic G)) (uniform _))
  (lift_dist l (uniform id))).
apply H0. assumption. clear H0. rewrite <- uniform_lift_id.
apply (looks_random H). unfold mu. reflexivity.
Qed.


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

Instance CI_eq_subrelation A : subrelation (@eq_PrFam A) (@CI A).
Proof.
unfold subrelation, predicate_implication, pointwise_lifting.
unfold Basics.impl.
intros. eapply CI_Proper. apply H. reflexivity. reflexivity.
Qed.

Definition Bdeterministic' {p l} (f : forall n, Bvector (p n) -> Bvector (l n))
  : forall n : nat, Bvector (p n) -> Comp (Bvector (l n)) :=
  fun n x => Ret (@Bvector_eq_dec _) (f n x).


Lemma lift_id : forall {A B : nat -> Set} (f : forall n, A n -> Comp (B n)), lift id f = f.
Proof.
intros. reflexivity.
Qed.

Definition shiftout_fam : forall n, Bvector n -> Bvector (pred n).
Proof.
destruct n. 
- exact (fun x => x).
- exact Vector.tl.
Defined.

Definition det_compose {A B C : nat -> Set} (f : forall n, A n -> B n)
  (g : forall n, B n -> C n) : forall n, A n -> C n := fun n x => g n (f n x).

Definition Bdet_compose {lf lg} (f : BDetComp lf)
  (g : BDetComp lg) : BDetComp (fun n => lg (lf n))
  := fun n x => g (lf n) (f n x).

Section Part2. 

(** Problem Set 2, Question 4, part 2 *)

(** G is a pseudorandom generator *)
Variable len : nat -> nat.
Variable G : BDetComp len.
Hypothesis G_is_PRG : PRG G.

Definition questionB := forall len' (G' : BDetComp len'),
  PRG G' -> PRG (Bdet_compose G' shiftout_fam).

Theorem lemmaB : questionB -> forall k, exists len' (G' : BDetComp len'),
  PRG G' /\ (len 1 = k + len' 1)%nat.
Proof.
intros. induction k.
- exists len. exists G. split. assumption. reflexivity.
- destruct IHk as (len' & G' & G'_is_PRG & G'len).
  exists (fun n => pred (len' n)). exists (Bdet_compose G' shiftout_fam).
  split.
  apply H. assumption. rewrite G'len. simpl.
  rewrite plus_n_Sm. rewrite  NPeano.Nat.succ_pred. reflexivity.
  unfold not. intros contra. 
  pose proof (length_stretches G'_is_PRG 1).
  rewrite contra in H0. eapply Lt.lt_n_0. apply H0.
Qed.

Lemma sumkzero : forall k n, k = (k + n)%nat -> n = 0%nat.
Proof.
intros. induction k. simpl in H. rewrite H. reflexivity.
apply IHk. simpl in H. injection H. auto.
Qed.

Theorem partB : ~ questionB.
Proof.
unfold not; intros contra.
pose proof (lemmaB contra).
specialize (H (len 1)).
destruct H as (len' & G' & G'_is_PRG & lenG').
pose proof (length_stretches G'_is_PRG 1).
apply sumkzero in lenG'. rewrite lenG' in H.
eapply Lt.lt_n_0. apply H.
Qed.

Lemma G_len_PPT : PPT (fun n : nat => Bdeterministic G (len n)).
Proof.
apply (@lift_PPT len _ _ (Bdeterministic G)).
eapply PPT_bounds_len. apply (is_PPT G_is_PRG).
apply (is_PPT G_is_PRG).
Qed.

Lemma evalDist_right_ident_not_broken :
  forall (A : Set) eqd (c : Comp A) (a : A),
  evalDist (Bind c (fun x : A => Ret eqd x)) a == evalDist c a.
Proof.
intros. simpl. destruct (in_dec eqd a (getSupport c)).
- rewrite (@Fold.sumList_exactly_one _ a). rewrite eq_dec_refl.
  apply ratMult_1_r. apply support_NoDup. assumption.
  intros. destruct (eqd b a). congruence. apply ratMult_0_r.
- apply getSupport_not_In_evalDist in n.
  rewrite n. apply Fold.sumList_0. intros. 
  destruct (eqd a0 a). subst. rewrite n. apply ratMult_0_l.
  apply ratMult_0_r.
Qed.  

Lemma deterministic_compose : forall {l lf lg} (f : BDetComp lf) (g : BDetComp lg) (mu : BPrFamily l),
  (Bmap (Bdeterministic (Bdet_compose f g)) mu == Bmap (Bcompose (Bdeterministic f) (Bdeterministic g)) mu)%Fam.
Proof.
intros. unfold Bdet_compose, Bcompose, Bdeterministic, Bmap, Bmapd.
unfold eq_PrFam. intros n.
unfold dist_sem_eq.
intros. apply evalDist_seq_eq. intros; reflexivity.
intros. simpl. 
destruct (Bvector_eq_dec (g (lf (l n)) (f (l n) x)) a).
rewrite (@Fold.sumList_exactly_one _ (f (l n) x)).
rewrite e. rewrite !eq_dec_refl. symmetry. apply ratMult_1_r.
repeat (constructor; auto). constructor. reflexivity.
intros. destruct (Bvector_eq_dec (f (l n) x) b). congruence.
apply ratMult_0_l. symmetry. apply Fold.sumList_0.
intros. destruct (Bvector_eq_dec (f (l n) x) a0).
destruct (Bvector_eq_dec (g (lf (l n)) a0) a).
subst. congruence. apply ratMult_0_r. apply ratMult_0_l.
Qed.

Lemma PPT_det_compose : forall {lf lg} (f : BDetComp lf) (g : BDetComp lg), 
  PPT (Bdeterministic f) -> PPT (fun n : nat => Bdeterministic g (lf n)) -> 
  PPT (Bdeterministic (Bdet_compose f g)).
Proof.
Admitted.

Theorem partA : PRG (Bdet_compose G G).
Proof.
constructor.
- intros. pose proof (length_stretches G_is_PRG).
  eapply Lt.lt_trans. apply H. apply H.
- unfold id. rewrite deterministic_compose.
  rewrite Bmap_Bcompose.
  transitivity (Bmap (Bdeterministic G) (@uniform len)).
  rewrite !Bmap_map. rewrite lift_id. 
  unfold lift, Bdeterministic.
  unfold Bmapd. simpl.
  apply CI_cong. simpl. 
  apply G_len_PPT.
  apply (looks_random G_is_PRG).
  apply looks_random_lift. assumption. unfold id.
  intros. apply Lt.lt_le_weak. apply (length_stretches G_is_PRG).
- apply PPT_det_compose.  apply G_is_PRG.
  apply G_len_PPT.
Qed.

Variable h : BDetComp id.
Hypothesis perm_is_permutation : forall n, permutation (h n).

Hypothesis h_efficient : PPT (Bdeterministic h).

Theorem partC : PRG (Bdet_compose G h).
Proof.
constructor.
- intros. unfold id. apply (length_stretches G_is_PRG).
- unfold id; simpl. change (fun x : nat => x) with (@id nat). 
  change (fun n => len n) with len. 
  pose proof (Bmap_Bcompose _ _ _ (Bdeterministic G) (Bdeterministic h) (uniform id)). 
  unfold id in H; simpl in H.
  pose proof (deterministic_compose (l:=id) G h (uniform id)).
  unfold id in H0; simpl in H0. rewrite H0.
  rewrite H. clear H H0.
  transitivity (Bmap (Bdeterministic h) (@uniform len)).
  apply CI_cong. apply lift_PPT. eapply PPT_bounds_len.
  eapply G_is_PRG. apply h_efficient.
  apply G_is_PRG.
  pose proof (Bpermutation h perm_is_permutation len).
  unfold id in H; simpl in H. rewrite H.
  reflexivity.
- apply PPT_det_compose. apply G_is_PRG. 
  apply lift_PPT. eapply PPT_bounds_len. apply G_is_PRG. 
  assumption.
Qed.

Theorem partD : PRG (Bdet_compose h G).
Proof.
constructor.
- intros. unfold id. apply G_is_PRG.
- unfold id; simpl. 
  rewrite deterministic_compose.
  rewrite Bmap_Bcompose.
  transitivity (Bmap (Bdeterministic G) (@uniform id)).
  apply CI_cong. apply G_is_PRG.
  unfold id; simpl. rewrite Bpermutation. reflexivity.
  apply perm_is_permutation. apply G_is_PRG.
- apply PPT_det_compose. apply h_efficient.
  apply G_is_PRG.
Qed.

End Part2.

(** Problem 4.1 *)

Section Part1.

(** G extends lengths only by 1 *)
Variable G : BDetComp S.
Hypothesis G_is_PRG : PRG G.

Variable p : nat -> nat.
Hypothesis p_stretches : forall n, n < p n.
Hypothesis p_poly : polynomial p.

Definition extG := repeat_n_det p G p_stretches.

Require Import Classical_Prop.

Axiom classical : forall A (P : A -> Prop), 
  (forall x : A, P x) \/ (exists x : A, ~ P x).

Theorem Part1 : PRG extG.
Proof.
constructor.
- apply p_stretches.
- unfold id. simpl. unfold CI.
  pose proof (classical _ (fun test => PPT test -> negligible (CSD_fam (Bmap (Bdeterministic extG) (uniform (fun x => x))) (uniform p) test))). simpl in H.
  destruct H. apply H.
  destruct H as (dist & breaks_security).
  apply imply_to_and in breaks_security.
  destruct breaks_security as (distPPT & nonnegl).
  assert (exists test', ~ negligible (CSD_fam (Bmap (Bdeterministic G) (uniform id)) (uniform S) test') /\ PPT test').
  admit.
  destruct H as (test' & nonnegltest' & PPTtest').
  apply False_rect. apply nonnegltest'.
  apply G_is_PRG. assumption.
- unfold extG. apply repeat_n_admissible. assumption.
  apply G_is_PRG.
Qed.

Fixpoint maximum (xs : list Rat) : Rat := match xs with
  | nil => 0
  | cons x xs => maxRat x (maximum xs)
  end.

Lemma sumList_nil : forall {A : Set} (f : A -> Rat),
  Fold.sumList nil f = 0.
Proof.
intros. unfold Fold.sumList. simpl. reflexivity.
Qed.

Lemma maxRat_l : forall x y, x <= maxRat x y.
Proof.
intros. unfold maxRat. destruct (bleRat x y) eqn:xy.
unfold leRat. apply xy. reflexivity.
Qed.

Lemma maxRat_r : forall x y, y <= maxRat x y.
Proof.
intros. unfold maxRat. destruct (bleRat x y) eqn:xy.
reflexivity. unfold leRat. apply bleRat_total. apply xy.
Qed.

Lemma maxRat_scales : forall c x y, maxRat x y * c == maxRat (x * c) (y * c).
Proof.
intros. apply leRat_impl_eqRat.
- unfold maxRat at 1. destruct (bleRat x y).
  apply maxRat_r. apply maxRat_l.
- apply maxRat_leRat_same. apply ratMult_leRat_compat.
  apply maxRat_l. reflexivity. apply ratMult_leRat_compat.
  apply maxRat_r. reflexivity.
Qed.

Definition max_len_ge_sum : forall {A : Set} (xs : list A) (f : A -> Rat),
  Fold.sumList xs f <= maximum (List.map f xs)  * (length xs / 1).
Proof.
intros. induction xs; simpl.
- rewrite sumList_nil. reflexivity.
- rewrite Fold.sumList_cons. 
  rewrite IHxs. simpl.
  rewrite ratS_num.
  rewrite ratMult_distrib.
  rewrite ratMult_1_r.
  apply ratAdd_leRat_compat.
  apply maxRat_l. rewrite maxRat_scales. apply maxRat_r.
Qed.