(** Import code from the Foundational Cryptography Framework (FCF) *)

Require Import Asymptotic Rat WC_PolyTime Admissibility Comp Bvector
               DetSem DistRules DistSem.

Local Open Scope rat.


(** Various unassorted but useful lemmas. *)

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

(** The composition of two polynomially-bounded functions
    is polynomially bounded. This is a well-known result,
    but with this representation of polynomial-boundedness, it is
    not very easy to prove, so I will just admit it as a lemma. *)
Theorem polynomial_compose : forall f g, polynomial f -> polynomial g
  -> polynomial (fun n => g (f n)).
Proof.
intros. unfold polynomial.
destruct H as (fx & fc1 & fc2 & Pf).
destruct H0 as (gx & gc1 & gc2 & Pg).
exists (gx * fx)%nat.
Admitted.




(** Function families from a family of types A to a family of types B. *)
Notation "A ~> B" := (forall n, A n -> Comp (B n)) (at level 70).

(** Composition of functions. *)
Definition comp {B C} (g : B -> C) {A} (f : A -> B) (x : A) : C := g (f x).

(** We will use the "@" sign for composition rather 
    than ∘ because it is easier to type. *)
Infix "@" := comp (at level 30).

Definition compose {A B C : nat -> Set} (f : A ~> B)
  (g : B ~> C) : A ~> C
  := fun n x => Bind (f n x) (g n).

(** Families of probability distributions. *)
Definition Dist (A : nat -> Set) := forall n, Comp (A n).








(** The FCF has a notion of "function cost models" which describe
    legitimate ways of assigning a
    numerical cost which is intended to be an upper bound on the maximum
    amount of time a function requires to be evaluated.

    However, it is not precise enough. In particular, the rules allow
    every function to be assigned cost 0, as the following code shows.
*)

(** A trivial function cost model which assigns 0 cost to everything. *)
Definition trivial_fcm : FunctionCostModel :=
  fun A B f x => True.

(** This trivial function cost model obeys all of the rules. *)
Theorem trivial_fcm_ok : function_cost_model trivial_fcm.
Proof.
unfold trivial_fcm; constructor; intros; auto.
Qed.

Section CSD.

(** From now on, we will assume a function cost model that satisfies
    the rules specified by the FCF. Noting that it is too weak,
    we will later add an axiom that it also satisfies.
*)
Variable fcm : FunctionCostModel.
Hypothesis fcm_facts : function_cost_model fcm.

Definition ccm : CompCostModel := comp_cost fcm.

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

(** This defines a way of assigning the cost of a probabilistic function from A to B
    in terms of the cost of a deterministic functions from A to B and cost of
    probabilistic expressions return something of type B. *)
Inductive prg_cost {A B} {f : A -> Comp B} {cost : nat} : Prop :=
  Mkcomp_cost : forall c1 c2, fcm _ _ f c1 -> (forall x, ccm _ (f x) c2) -> (c1 + c2 <= cost)%nat -> prg_cost.

Arguments prg_cost {A} {B} f cost : clear implicits.

(** Lift costs on functions to sequences of costs on function families. *)
Definition prog_cost {A B} (f : A ~> B) (cost : nat -> nat) : Prop :=
  forall n, prg_cost (f n) (cost n).

Axiom cost_of_Bind : forall (A B C : Set) (f : A -> Comp B) (c : B -> Comp C) (cost : nat),
  fcm A (Comp B) f cost ->
  fcm A (Comp C) (fun x => Bind (f x) c) cost.

Lemma compose_cost : forall {A B C : nat -> Set} (f : forall n, A n -> Comp (B n)) (g : forall n, B n -> Comp (C n)) costf costg,
  prog_cost f costf -> prog_cost g costg
  -> prog_cost (compose f g) (fun n => costf n + costg n)%nat.
Proof.
intros. unfold prog_cost in *. 
intros n. specialize (H n). specialize (H0 n).
induction H, H0. econstructor. simpl. instantiate (1 := c1).
replace c1 with (c1 + 0 + 0)%nat by omega.
unfold compose. rewrite <- !plus_n_O.
apply cost_of_Bind. assumption.
intros x. simpl. eapply comp_cost_Bind. simpl.
unfold ccm in *. apply H1. apply H0.
intros. apply H3. eapply Le.le_trans. Focus 2. 
apply Plus.plus_le_compat; eassumption.
omega.
Qed.

Inductive PPT {A B} {f : A ~> B} : Prop :=
  IsPPT : forall cost, prog_cost f cost -> polynomial cost -> PPT.

Arguments PPT {A} {B} f : clear implicits.

Definition reindex (p : nat -> nat) {A B : nat -> Set} (f : A ~> B)
  : A @ p ~> B @ p := fun n => f (p n).

Lemma reindex_cost : forall (p : nat -> nat) A B (f : A ~> B) cost,
  prog_cost f cost -> prog_cost (fun n => f (p n)) (fun n => cost (p n)).
Proof.
unfold prog_cost. intros. apply (H (p n)).
Qed.

Fixpoint repeat_k {A : nat -> Set} (k : nat) (f : forall n, A n -> A (S n))
  : forall n, A n -> A (k + n)%nat := match k as k' return forall n, A n -> A (k' + n)%nat with
  | 0 => fun n x => x
  | S k' => fun n x => f _ (repeat_k k' f n x)
  end.

Definition repeat_n {A : nat -> Set} (p : nat -> nat) (f : forall n, A n -> A (S n))
  : forall n, A n -> A (p n - n + n)%nat
  := fun n => repeat_k (p n - n)%nat f n.

Definition repeat_n_correct_ty {A : nat -> Set} p (pmono : forall n, (n <= p n)%nat)(f : forall n, A n -> A (S n))
  : forall n, A n -> A (p n).
Proof.
intros n.
rewrite (Minus.le_plus_minus _ _ (pmono n)).
rewrite Plus.plus_comm.
apply (repeat_n p f).
Defined.

Definition Bmapd {A n} (f : A -> Bvector n) := fun x => Ret (@Bvector_eq_dec _) (f x).

Definition BComp (length : nat -> nat) := forall n, Bvector n -> Comp (Bvector (length n)).

Definition Bdeterministic {l} (f : forall n, Bvector n -> Bvector (l n))
  : BComp l := fun n => Bmapd (f n).

Theorem repeat_n_admissible : forall (f : forall n, Bvector n -> Bvector (S n))
  (p : nat -> nat) (pmono : forall n, n < p n), polynomial p ->
  PPT (Bdeterministic f) -> PPT (Bdeterministic (repeat_n p f)).
Proof.
intros. induction H0.
apply IsPPT with (fun n => p n * cost (p n))%nat.
admit.
apply polynomial_mult; try assumption.
apply polynomial_compose; assumption.
Admitted.

Lemma PPT_compose : forall {A B C : nat -> Set} (f : A ~> B) (g : B ~> C),
  PPT f -> PPT g -> PPT (compose f g).
Proof.
intros. destruct H, H0.
econstructor. 
apply compose_cost; eassumption.
apply polynomial_plus; assumption.
Qed.

Require Import Rat.

Local Open Scope rat.

Infix "==" := dist_sem_eq : Dist_scope.
Delimit Scope Dist_scope with Dist.

(** The computational statistical distance of two probability distributions
    with respect to a (probabilistic) test algorithm. *)
Definition CSD {A} (mu1 mu2 : Comp A) (test : A -> Comp bool)
  := | Pr [ Bind mu1 test ] - Pr [ Bind mu2 test ] |.

(** Several nice properties of the computational statistical distance. *)
Lemma CSD_refl {A} : forall (mu : Comp A) (test : A -> Comp bool),
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
  
Definition reindex_Dist {A} (p : nat -> nat) (mu : Dist A) : Dist (A @ p)
  := fun n => mu (p n).

Definition Distinguisher (A : nat -> Set) := A ~> (fun _ => bool).

Definition ap {A B : nat -> Set} (f : A ~> B) (mu : Dist A) : Dist B
  := fun n => Bind (mu n) (f n).

Definition eq_Dist A (x y : Dist A) : Prop :=
  forall n, (x n == y n)%Dist.

Instance eq_Dist_Equivalence : forall A, Equivalence (@eq_Dist A).
Proof.
intros. constructor; 
unfold Reflexive, Symmetric, Transitive, eq_Dist; intros.
reflexivity. symmetry. apply H.
transitivity (y n). apply H. apply H0. 
Qed.

Notation "x ={ A }= y" := (eq_Dist A x y) (at level 70) : Fam_scope.
Infix "==" := (eq_Dist _) : Fam_scope. 
Delimit Scope Fam_scope with Fam.

Theorem ap_compose : forall {A B C : nat -> Set} (f : A ~> B) (g : B ~> C)
  (mu : Dist A),
  (ap g (ap f mu) ={ C }= ap (compose f g) mu)%Fam.
Proof.
intros. unfold eq_Dist. intros.
unfold map. simpl. apply evalDist_assoc_eq.
Qed.

(** Computational statistical distance for a pair of families
    of probability distributions with respect to a family
    of distinguishers. *)
Definition CSD_fam {A : nat -> Set} (mu1 mu2 : Dist A)
  (test : Distinguisher A) (n : nat) : Rat :=
  CSD (mu1 n) (mu2 n) (test n).

(** The definition of computational indistinguishability of two
    families of probability distributions. *)
Definition CI (A : nat -> Set) (mu1 mu2 : Dist A) : Prop :=
  forall test : Distinguisher A, PPT test ->
    negligible (CSD_fam mu1 mu2 test).

(** Notations for representing computational indistinguishability. *)
Infix "~~" := (CI _) (at level 70).
(*Notation "x ~{ A }~ y" := (CI A x y) (at level 70).*)



(** The next several proofs show that computational indistinguishability
    indeed forms an equivalence relation that is respected by PPT
    functions.
*)

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

Lemma CI_refl {A} : forall (mu : Dist A), mu ~~ mu.
Proof.
unfold CI. intros. eapply negligible_eq. apply negligible_zero. 
intros. simpl. unfold CSD_fam. rewrite CSD_refl.
reflexivity.
Qed.

Lemma CI_sym {A} : forall (mu1 mu2 : Dist A), mu1 ~~ mu2 -> mu2 ~~ mu1.
Proof.
unfold CI. intros. eapply negligible_eq. apply H. eassumption.
intros. apply CSD_sym.
Qed.

Lemma CI_trans {A} : forall (a b c : Dist A), a ~~ b -> b ~~ c -> a ~~ c.
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

Lemma CI_cong {A B} : forall (a b : Dist A) (f : forall n, A n -> Comp (B n)),
  PPT f -> a ~~ b -> ap f a ~~ ap f b.
Proof.
unfold CI. intros.
assert (forall n, CSD_fam (ap f a) (ap f b) test n == CSD_fam a b (compose f test) n).
intros. unfold CSD_fam, ap. simpl. unfold CSD. 
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


(** The next set of lemma ("Instances") just say that several constructions
    respect equivalence relations on their arguments. Declaring these instances
    is useful for automatic rewriting of goals. *)
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

Instance CSD_fam_Proper : forall A, Proper (eq_Dist A ==> eq_Dist A ==> eq ==> pointwise_relation _ eqRat) (@CSD_fam A).
Proof.
intros. unfold Proper, respectful, pointwise_relation.
intros. unfold CSD_fam. subst. unfold eq_Dist in *.
rewrite (H a), (H0 a). reflexivity.
Qed.

Instance negligible_Proper : Proper (pointwise_relation _ eqRat ==> iff) negligible.
Proof.
unfold Proper, respectful, pointwise_relation.
intros. split; intros; eapply negligible_eq; eauto.
intros. symmetry. apply H.
Qed.

Instance CI_Proper : forall A, Proper (eq_Dist A ==> eq_Dist A ==> iff) (@CI A).
Proof.
unfold Proper, respectful, CI. intros. split; intros.
- rewrite <- H, <- H0. apply H1; assumption.
- rewrite H, H0. apply H1; assumption.
Qed.





(** The next several lemmas build up to a theorem that says
    that computational indistinguishability is preserved by
    functions p : nat -> nat satisfying
    forall n, n <= p n.
    Intuitively, this is because we are going towards more
    indistinguishable distributions even faster, so it
    should be relatively obvious! However, the proof relies
    on "un-reindexing" a distinguisher, that is,
    taking a 
    test : Distinguisher (A @ p)
    and producing a 
    test' : Distinguisher A
    which distinguishes just as well. The distinguisher works
    test' works by finding an inverse for the function p,
    in order to see where to run the previous distinguisher.
*)

(** Given an infinite sequence of true-false values, we can check
    whether there are any "true" values up until a given bound
    (in time linear in the bound). *)
Fixpoint bounded_lookup (p : nat -> bool) (bound : nat) :
 { n | p n = true } + (forall n, (n <= bound)%nat -> p n = false).
Proof. 
induction bound.
- destruct (p 0%nat) eqn:p0. 
  refine (inl (exist (fun n => p n = true) 0%nat p0)).
  right. intros. apply Le.le_n_0_eq in H.
  subst. assumption.
- destruct IHbound. 
  refine (inl s).
  destruct (p (S bound)) eqn:ps.
  refine (inl (exist (fun n => p n = true) (S bound) ps)).
  right. intros. destruct (Compare_dec.le_lt_dec (S bound) n).
  assert (n = S bound) by (apply Le.le_antisym; assumption).
  subst. assumption. unfold lt in l.
  apply e. apply Le.le_S_n. assumption.
Defined.

(** We use this decider to create a partial inverse
    for a sequence. *)
Fixpoint pmono_partial_inverse (p : nat -> nat)
 (n : nat) : { k | p k = n } + (forall k, (k <= n)%nat -> p k <> n).
Proof.
pose (bounded_lookup (fun k => EqNat.beq_nat (p k) n) n) as ans.
destruct ans.
destruct s.
rewrite EqNat.beq_nat_true_iff in e.
refine (inl (exist _ x e)).
right. intros. apply EqNat.beq_nat_false_iff. apply e.
assumption.
Defined.

(** This partial inverse will always successfully find
    an inverse when there is one. *)
Definition pmono_partial_inverse_complete (p : nat -> nat)
  (pmono : forall n, (n <= p n)%nat)
  : forall k : nat, exists k' prf, pmono_partial_inverse p (p k) = inl (exist _ k' prf).
Proof.
intros k.
destruct (pmono_partial_inverse p (p k)).
destruct s as (k' & prf). exists k'. exists prf. reflexivity.
pose proof (n k (pmono k)). congruence.
Qed.

(** The "always_true" distinguisher is useless, always returning
    "true" as the name suggests. We call this distinguisher when
     we fail to find an inverse. *)
Definition always_true {A} : A -> Comp bool := fun _ => Ret bool_dec true.

(** Un-reindex a distinguisher. *)
Definition unreindex_distinguisher {p A} 
  (pmono : forall n, (n <= p n)%nat)
  (f : Distinguisher (A @ p))
  : Distinguisher A.
Proof.
unfold Distinguisher, comp in *.
intros n.
refine (match pmono_partial_inverse p n with
  | inr _ => always_true
  | inl (exist k prf) => eq_rect (p k) (fun i => A i -> Comp bool) (f k) n prf
  end).
Defined.

(** The unreindexed distinguisher runs in polynomial time.
    First, the unreindexed distinguisher checks for a partial inverse,
    where the bound is equal to the security parameter, so this takes
    linear time. Then, it either runs the trivially true distinguisher,
    or the distinguisher of "f" at a lower value of the security parameter,
    and since "f" is polynomial time in its security parameter, this will
    certainly be polynomial time in this security parameter. *)
Theorem unreindex_distinguisher_PPT {p A}
  (pmono : forall n, (n <= p n)%nat) (f : Distinguisher (A @ p))
  : PPT f -> PPT (unreindex_distinguisher pmono f).
Proof.
Admitted.

Require Import Eqdep_dec.

(** The unreindexed distinguisher produces the same output as the
    original distinguisher whenever it manages to find an inverse.
    The "pinj" constraint supposes that the reindexing function 'p'
    is injective. This makes the proof that the reindexed distinguisher
    preserves computational indistinguishability simpler. Otherwise,
    we would have to say that the unreindexed distinguisher only
    has the same result infinitely often (rather than always),
    making the proof trickier. *)
Theorem unreindex_distinguisher_behaves {p A}
  (pmono : forall n, (n <= p n)%nat) (f : Distinguisher (A @ p))
  (pinj : forall m n, p m = p n -> m = n)
  : forall (mu : Dist A) n, dist_sem_eq 
     (Bind (mu (p n)) (f n))
     (Bind (mu (p n)) (unreindex_distinguisher pmono f (p n))).
Proof.
intros. unfold unreindex_distinguisher.
pose proof (pmono_partial_inverse_complete p pmono n).
destruct H as (k' & prf & isSome).
rewrite isSome. clear isSome.
pose proof (pinj _ _ prf). induction H. 
rewrite <- (eq_rect_eq_dec Peano_dec.eq_nat_dec).
reflexivity.
Qed.

Lemma unreindex_distinguisher_CSD_fam {p A}
  (pmono : forall n, (n <= p n)%nat) (f : Distinguisher (A @ p))
  (pinj : forall m n, p m = p n -> m = n)
  : forall (mu1 mu2 : Dist A), pointwise_relation nat eqRat
    (CSD_fam (reindex_Dist p mu1) (reindex_Dist p mu2) f)
    (CSD_fam mu1 mu2 (unreindex_distinguisher pmono f) @ p).
Proof.
intros. unfold pointwise_relation. intros n.
unfold CSD_fam, CSD, reindex_Dist, comp.
rewrite (unreindex_distinguisher_behaves pmono f pinj mu1 n true).
rewrite (unreindex_distinguisher_behaves pmono f pinj mu2 n true).
reflexivity.
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

(** This is essentially the final theorem, which says that
    reindexing doesn't affect computational indistinguishability
    for suitably "nice" reindexers. *)
Lemma lift_CI' {A} (p : nat -> nat) (mu1 mu2 : Dist A)
  (pmono : forall n, (n <= p n)%nat)
  (pinj : forall m n, p m = p n -> m = n)
  : mu1 ~~ mu2 -> reindex_Dist p mu1 ~~ reindex_Dist p mu2.
Proof.
unfold CI. intros. simpl.
specialize (H (unreindex_distinguisher pmono test) 
  (unreindex_distinguisher_PPT pmono test H0)).
rewrite (unreindex_distinguisher_CSD_fam pmono test pinj mu1 mu2).
apply negligible_compose_fast. apply pmono. assumption.
Qed.

(** this just lies to get rid of one of the assumptions *)
Lemma lift_CI {A} (p : nat -> nat) (mu1 mu2 : Dist A)
  (pmono : forall n, (n <= p n)%nat)
  : mu1 ~~ mu2 -> reindex_Dist p mu1 ~~ reindex_Dist p mu2.
Proof.
intros. apply lift_CI'; try assumption.
admit.
Qed.


Theorem eq_dec_refl {A} (de : eq_dec A) (x : A) {B} (t f : B) : 
  (if de x x then t else f) = t.
Proof.
destruct (de x x). reflexivity. congruence.
Qed.










Definition BDist (length : nat -> nat) := forall n, Comp (Bvector (length n)).

Definition uniform l : BDist l := fun n => Rnd (l n).

Lemma uniform_lift_id {l} : uniform l = reindex_Dist l (uniform id).
Proof. 
reflexivity.
Qed.

Definition Bcompose {l1 l2} (f : BComp l1) (g : BComp l2)
  : BComp (fun n => l2 (l1 n))
  := fun n x => Bind (f n x) (g (l1 n)).

Definition Bmap {lf lmu} (f : BComp lf) (mu : BDist lmu)
  : BDist (fun n => lf (lmu n))
  := fun n => Bind (mu n) (f (lmu n)).

Lemma Bmap_Bcompose : forall l l1 l2 (f : BComp l1) (g : BComp l2),
  forall (mu : BDist l), (Bmap (Bcompose f g) mu == Bmap g (Bmap f mu))%Fam.
Proof.
intros.
unfold Bmap, Bcompose, eq_Dist.
intros. symmetry. apply evalDist_assoc_eq.
Qed.

Lemma Bmap_ap {l lf} : forall (f : BComp lf) (mu : BDist l),
  Bmap f mu = ap (reindex l f) mu.
Proof.
intros. unfold Bmap, ap. simpl. reflexivity.
Qed.

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

Definition BDetComp (l : nat -> nat) := forall n, Bvector n -> Bvector (l (n)).

Record PRG {l : nat -> nat} {G : BDetComp l} :=
  { length_stretches : forall n, n < l n
  ; looks_random : Bmap (Bdeterministic G) (uniform id) ~~ uniform l
  ; is_PPT : PPT (Bdeterministic G)
  }.

Arguments PRG {l} G : clear implicits.

Lemma ap_reindex : forall {A B : nat -> Set} (f : forall n, A n -> Comp (B n)) p mu, ap (reindex p f) (reindex_Dist p mu)
  = reindex_Dist p (ap f mu).
Proof.
intros. unfold map, reindex_Dist. simpl. reflexivity.
Qed.

Lemma looks_random_lift {l G} : @PRG l G
  -> forall (p : nat -> nat) (pmono : forall n, (n <= p n)%nat)
  , Bmap (Bdeterministic G) (uniform p) ~~ uniform (l @ p).
Proof.
intros. rewrite (Bmap_ap (Bdeterministic G)).
rewrite (@uniform_lift_id p).
rewrite (@uniform_lift_id (l @ p)).
rewrite (ap_reindex (Bdeterministic G) p). 
pose (mu := reindex_Dist p (reindex_Dist l (@uniform id))).
unfold comp, id in mu.
transitivity mu. unfold mu.
pose proof (@lift_CI (fun x => Bvector (l x)) p
  (ap (Bdeterministic G) (uniform _))
  (reindex_Dist l (uniform id))).
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

Lemma reindex_PPT : forall (p : nat -> nat) {A B}
  (f : forall n, A n -> Comp (B n)),
  polynomial p ->
  PPT f -> PPT (fun n => f (p n)).
Proof.
intros. induction H0. econstructor.
apply reindex_cost. eassumption.
apply polynomial_compose; assumption.
Qed.

Instance CI_eq_subrelation A : subrelation (@eq_Dist A) (@CI A).
Proof.
unfold subrelation, predicate_implication, pointwise_lifting.
unfold Basics.impl.
intros. eapply CI_Proper. apply H. reflexivity. reflexivity.
Qed.

Definition Bdeterministic' {p l} (f : forall n, Bvector (p n) -> Bvector (l n))
  : forall n : nat, Bvector (p n) -> Comp (Bvector (l n)) :=
  fun n x => Ret (@Bvector_eq_dec _) (f n x).


Lemma reindex_id : forall {A B : nat -> Set} (f : A ~> B), 
  reindex id f = f 
  :> (A @ id ~> B @ id).
Proof.
intros. reflexivity.
Qed.

Definition shiftout_fam : forall n, Bvector n -> Bvector (pred n) := 
  fun n => match n with
  | 0 => fun x => x
  | S n' => Vector.shiftout
  end.

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

(** The statement for problem B asks whether it universally holds that
    composing G with the "shiftout" function, which simply drops the final
    bit of a bitvector, still results in a pseudorandom generator. *)
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


(** The solution to Part B, is that no, such a statement is false
    (given that we have assumed the presence of at least a single
     pseudorandom generator, no matter what its length function looks like. *)
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
apply (@reindex_PPT len _ _ (Bdeterministic G)).
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

Lemma deterministic_compose : forall {l lf lg} (f : BDetComp lf) (g : BDetComp lg) (mu : BDist l),
  (Bmap (Bdeterministic (Bdet_compose f g)) mu == Bmap (Bcompose (Bdeterministic f) (Bdeterministic g)) mu)%Fam.
Proof.
intros. unfold Bdet_compose, Bcompose, Bdeterministic, Bmap, Bmapd.
unfold eq_Dist. intros n.
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

(** The solution to part A: If I compose G with itself, the result is
    a pseudorandom generator. *)
Theorem partA : PRG (Bdet_compose G G).
Proof.
constructor.
- intros. pose proof (length_stretches G_is_PRG).
  eapply Lt.lt_trans. apply H. apply H.
- unfold id; rewrite deterministic_compose.
  rewrite Bmap_Bcompose.
  transitivity (Bmap (Bdeterministic G) (@uniform len)).
  rewrite !Bmap_ap;
  apply CI_cong; [apply G_len_PPT |];
  replace (reindex (fun x : nat => x) (Bdeterministic G))
    with (Bdeterministic G) by reflexivity;
  unfold reindex, Bdeterministic.
  apply (looks_random G_is_PRG).
  apply looks_random_lift; [ assumption |
    intros; apply Lt.lt_le_weak; apply (length_stretches G_is_PRG) ].
- apply PPT_det_compose.  apply G_is_PRG.
  apply G_len_PPT.
Qed.

(** For parts c and d, I must first define permutations and give some simple
    properties about them.
*)


Inductive permutation {A B} {f : A -> B} :=
  { f_inv : B -> A
  ; to_from : forall a, f_inv (f a) = a
  ; from_to : forall b, f (f_inv b) = b
  }.

Arguments permutation {A} {B} f : clear implicits.

Definition map_prob {A B : Set} (de : eq_dec B) (f : A -> B) (mu : Comp A) : Comp B
  := Bind mu (fun x => Ret de (f x)).

(** A permutation of the uniform distribution
    is a uniform distribution. *)
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

(** Puts the above result in a clearer format. *)
Theorem perm_uniform_Bvector : forall n
  (f : Bvector n -> Bvector n),
  permutation f -> 
  (@Rnd n == map_prob (@Bvector_eq_dec n) f (@Rnd n))%Dist.
Proof.
intros.
unfold dist_sem_eq.
intros. symmetry. apply perm_uniform. assumption. unfold evalDist.
unfold eqRat, beqRat. simpl. congruence.
intros. apply uniformity.
Qed.

(** Another restatement of the result. *)
Definition Bpermutation (f : forall n, Bvector n -> Bvector n) 
  (permf : forall n, permutation (f n))
  (l : nat -> nat)
  : (Bmap (Bdeterministic f) (uniform l) == uniform l)%Fam.
Proof.
unfold eq_Dist. intros n.
unfold Bmap, Bdeterministic, uniform.
pose proof perm_uniform_Bvector as H.
unfold map_prob in H. symmetry. apply H.
apply permf.
Qed.

(** We assume that "h" is a permutation, as in the problem set. *)
Variable h : BDetComp id.
Hypothesis h_is_permutation : forall n, permutation (h n).

Hypothesis h_efficient : PPT (Bdeterministic h).

(** The answer to part C: composing G with a permutation
    does result in a pseudorandom generator. *)
Theorem partC : PRG (Bdet_compose G h).
Proof.
constructor.
- intros. apply (length_stretches G_is_PRG).
- unfold id; simpl; change (fun x : nat => x) with (@id nat);
  change (fun n => len n) with len;
  pose proof (deterministic_compose (l:=id) G h (uniform id)) as H0;
  unfold id in H0; simpl in H0; rewrite H0; clear H0.
  pose proof (Bmap_Bcompose _ _ _ (Bdeterministic G) (Bdeterministic h) (uniform id))
   as H; unfold id in H; simpl in H; rewrite H; clear H.
  transitivity (Bmap (Bdeterministic h) (@uniform len)).
  apply CI_cong. apply reindex_PPT. eapply PPT_bounds_len;
  eapply G_is_PRG. apply h_efficient.
  apply G_is_PRG.
  rewrite Bpermutation.
  reflexivity. assumption.
- apply PPT_det_compose. apply G_is_PRG. 
  apply reindex_PPT. eapply PPT_bounds_len; apply G_is_PRG. 
  assumption.
Qed.

(** The answer to part D: composing a permutation with G
    does result in a pseudorandom generator. *)
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
  apply h_is_permutation. apply G_is_PRG.
- apply PPT_det_compose. apply h_efficient.
  apply G_is_PRG.
Qed.

End Part2.

(** Problem 4.1 *)
(** Unfortunately, I only made partial progress on this. *)

Section Part1.

(** G extends lengths only by 1 *)
Variable G : BDetComp S.
Hypothesis G_is_PRG : PRG G.

Variable p : nat -> nat.
Hypothesis p_stretches : forall n, n < p n.
Hypothesis p_poly : polynomial p.

Definition p_mono : forall n, (n <= p n)%nat.
Proof.
intros. apply Lt.lt_le_weak. apply p_stretches.
Qed.

Definition extG := repeat_n p G.


(** Here, we allow ourselves to use classical logic, so that we can do a proof by contradiction.
    That is, "Suppose there were a succesful distinguisher on the construction. Then we can
    find a successful distinguisher on the original pseudorandom generator. *)
Require Import Classical_Prop.

Axiom classical : forall A (P : A -> Prop), 
  (forall x : A, P x) \/ (exists x : A, ~ P x).


(** This sketches the main format of the proof. *)
Theorem Part1 : PRG extG.
Proof.
constructor.
- intros. rewrite Plus.plus_comm. 
  rewrite Minus.le_plus_minus_r. apply p_stretches. 
  apply Lt.lt_le_weak. apply p_stretches.
- unfold id. simpl. unfold CI.
  pose proof (classical _ (fun test => PPT test -> negligible (CSD_fam (Bmap (Bdeterministic extG) (uniform (fun x => x))) (uniform _) test))). simpl in H.
  destruct H. apply H.
  destruct H as (dist & breaks_security).
  apply imply_to_and in breaks_security.
  destruct breaks_security as (distPPT & nonnegl).
  assert (exists test', ~ negligible (CSD_fam (Bmap (Bdeterministic G) (uniform id)) (uniform S) test') /\ PPT test').
  admit.
  destruct H as (test' & nonnegltest' & PPTtest').
  apply False_rect. apply nonnegltest'.
  apply G_is_PRG. assumption.
- unfold extG. unfold repeat_n_correct_ty. apply repeat_n_admissible; try assumption.
  apply G_is_PRG.
Qed.

(** This defines a triangular (2-dimensional) family of distributions,
    of the form
    G^k (Uniform[n]),
    which are distributions of length (k + n). *)

Definition G_distribution (n k : nat) : Comp (Bvector (k + n)) :=
  Bind (Rnd n) (fun x => Ret (@Bvector_eq_dec (k + n)) (repeat_k k G _ x)).

(** Compute the bound using the triangle inequality that

   Distance (G^k(Uniform[n]), Uniform[n + k])
      <= Sum_{i = 0}^k  Distance(G^i(Uniform[n + k - i]), G^{i + 1}(Uniform[n + k - i - 1]))
*)
Fixpoint G_distribution_dist_bound (n k : nat) : (Bvector (k + n) -> Comp bool) -> Rat :=
  match k as k' return (Bvector (k' + n) -> Comp bool) -> Rat with
  | 0 => fun _ => 0
  | S k' => fun test =>
    let mu := (eq_rect _ (fun m => Comp (Bvector m)) (G_distribution n (S k')) _ (plus_n_Sm _ _)) in
    let test' := (eq_rect _ (fun m => Bvector m -> Comp bool) test _ (plus_n_Sm _ _)) in
    CSD (G_distribution (S n) k') mu test'
         + G_distribution_dist_bound (S n) k' test'
  end.

Lemma right_ident_dist_sem_eq :
  forall (A : Set) (eqd : eq_dec A) (c : Comp A),
  ((Bind c (fun x => Ret eqd x)) == c)%Dist.
Proof.
intros. unfold dist_sem_eq. 
intros. apply evalDist_right_ident_not_broken.
Qed.
     
(** Here I prove that the bound using the repeated triangle inequality holds. *)
Lemma CSD_G_triangle : forall n k (test : Bvector (k + n) -> Comp bool),
  CSD (Rnd (k + n)) (G_distribution n k) test <= 
  G_distribution_dist_bound n k test.
Proof.
intros. generalize dependent n. induction k; intros. 
- unfold G_distribution. simpl. 
  apply eqRat_impl_leRat.
  rewrite right_ident_dist_sem_eq.
  apply CSD_refl.
- simpl. specialize (IHk (S n) (eq_rect (S (k + n)) (fun m : nat => Bvector m -> Comp bool) test
        (k + S n)%nat (plus_n_Sm k n))).
  rewrite <- IHk.
  (** This statement says that
     Distance (Random, G_distribution(n, S k)) <=
        Distance (G_distribution(S n, k), G_distribution(n, S k))
      + Distance (Random, G_distribution(S n, k))
    which is clearly just an instance of the triangle inequality!
    Unfortunately, I can't get the types to match up. Just a technical issue.
    I will admit defeat.
  *)
  admit.
Admitted.

(** The next set of lemmas works towards finding that the
    maximum of non-negative numbers in a list, multiplied by
    the list's length, is at least the sum of those numbers. *)
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

End Part1.







(** DEAD CODE *)

(** If we chop off one bit from the uniform distribution, the result is still uniform. *)
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

(** Chop k bits off of a bitvector. *)
Fixpoint truncate k : forall n, Bvector (k + n) -> Bvector n :=
  match k as k' return forall n, Bvector (k' + n) -> Bvector n  with
  | 0 => fun n x => x
  | S k' => fun n x => truncate k' n (Vector.tl x)
  end.

(** If we truncate a uniformly sampled bitvector by taking off [k] bits, the
    result is still uniform. *)
Lemma truncate_uniform : forall k n, (Bind (Rnd (k + n)) (Bmapd (truncate k n)) == Rnd n)%Dist.
Proof.
intros k. induction k.
- simpl. unfold truncate. simpl. unfold Bmapd.
  intros n. unfold dist_sem_eq. 
  intros x. apply evalDist_right_ident.
- intros n. simpl. rewrite Bmapd_compose2.
  rewrite tl_uniform. fold plus. apply IHk.
Qed.



End CSD.     
