Require Import Template.monad_utils
        Template.Ast
        (* Template.AstUtils *)
        Template.TemplateMonad
        Template.LiftSubst.
        (* Template.Checker *)
        (* Template.Typing *)
        (* Template.Induction. *)

Require Import Translations.translation_utils.

Require Import Forcing.TemplateForcing
Forcing.translation_utils_bis.


Require Import List.



Import MonadNotation.
Import ListNotations.


Require Import BasicsMisc.
Require Import Hott_lemmas.
Require Import Simple_arithmetic.
Require Import Cubes.
Require Import Monotonicity.
Require Import Cartesian.
Require Import Forcing_I.


(** Face lattice *)


(* Eval compute in Cof_to_Prop (ForAllCof (fun i => ForAllCof (fun j => OrCof (Cof0 i) (Cof1 j)))).  *)




Definition last_finset (n : nat) : finset (S n).
  exists n. easy.
Defined.

Definition finset_inj (n : nat) : finset n -> finset (S n).
  intros [m p]. exists m. apply le_S. exact p.
Defined.









Definition isEquiv (A B : Type) : Type :=
  Σ (f : A -> B) (g : B -> A), (f o g = fun x => x) /\ (g o f = fun x => x).

Notation "A ≅ B" := (isEquiv A B) (at level 65, left associativity).

Run TemplateProgram (TC1 <-  Translate ax4_TC "fcompose" ;;
                          TC2 <-  Translate TC1 "isEquiv" ;;
                         tmDefinition "isEq_TC" TC2).

Definition projEq1' {p : nat}
           {A B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
  : isEquivᵗ p A B p id ->
    (forall (p0 : nat) (α : p ~> p0),
        (forall (p1 : nat) (α0 : p0 ~> p1),
            A p1 (α0 ô α) p1 id) -> B p0 α p0 id
    ).
  intros [x _]. exact x.
Defined.

Definition projEq2' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
  : isEquivᵗ p A B p id -> (forall (p0 : nat) (α : p ~> p0),
                              (forall (p1 : nat) (α0 : p0 ~> p1), B p1 (α0 ô α) p1 id) ->
                              A p0 α p0 id).
  intros [x y]. destruct (y p id) as [z _]. exact z.
Defined.

Definition projEq3' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           (ie : isEquivᵗ p A B p id)
           : (forall (p0 : 𝐂_obj) (α : p ~> p0),
                 eqᵗ p0
                     (fun (p1 : nat) (α0 : p0 ~> p1) (p2 : nat) (α1 : p1 ~> p2) =>
                        (forall (p3 : nat) (α2 : p2 ~> p3),
                            B p3 (α2 ô α1 ô α0 ô α) p3 id) ->
                        B p2 (α1 ô α0 ô α) p2 id)
                     (fun (p1 : nat) (α0 : p0 ~> p1) =>
                        fcomposeᵗ p1
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     B p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     A p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     B p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) => projEq1' ie p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) => projEq2' ie p2 (α1 ô α0 ô α)))
                     (fun (p1 : nat) (α0 : p0 ~> p1)
                        (x : forall (p2 : nat) (α1 : p1 ~> p2),
                            B p2 (α1 ô α0 ô α) p2 id) =>
                        x p1 id)).
  destruct ie as [x y]. simpl.
  destruct (y p id) as [z t]. destruct (t p id) as [a b].
  exact a.
Defined.

Definition projEq4' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           (ie : isEquivᵗ p A B p id)
           : (forall (p0 : 𝐂_obj) (α : p ~> p0),
                 eqᵗ p0
                     (fun (p1 : nat) (α0 : p0 ~> p1) (p2 : nat) (α1 : p1 ~> p2) =>
                        (forall (p3 : nat) (α2 : p2 ~> p3),
                            A p3 (α2 ô α1 ô α0 ô α) p3 id) ->
                        A p2 (α1 ô α0 ô α) p2 id)
                     (fun (p1 : nat) (α0 : p0 ~> p1) =>
                        fcomposeᵗ p1
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     A p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     B p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     A p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) => projEq2' ie p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) => projEq1' ie p2 (α1 ô α0 ô α)))
                     (fun (p1 : nat) (α0 : p0 ~> p1)
                        (x : forall (p2 : nat) (α1 : p1 ~> p2),
                            A p2 (α1 ô α0 ô α) p2 id) =>
                        x p1 id)).
  destruct ie as [x y]. simpl. destruct (y p id) as [z t]. destruct (t p id) as [a b]. exact b.
Defined.


(* Run TemplateProgram (tImplementTC covers_TC "covers_F1_TC" "covers_F1" (forall i : I, (covers (F1 i)) -> (i = I1))). *)

(* Inductive boolᵗ (p : nat) : Type := trueᵗ : boolᵗ p *)
(*                                 | falseᵗ : boolᵗ p. *)

(* Locate bool. *)


(* Fixpoint covers (f : F) : Prop. *)
(* Proof. *)
(*   destruct f.  *)
(*   - exact (i = I1). *)
(*   - exact (i = I0). *)
(*   - exact (or (covers f1) (covers f2)). *)
(*   - exact (and (covers f1) (covers f2)). *)
(*   - exact (forall i : I, (covers (f i))). *)
(* Defined. *)

(* Run TemplateProgram (TC1 <- tAddExistingInd Ft_TC "Coq.Init.Datatypes.bool" "boolᵗ" ;; *)
(*                           tmDefinition "bool_TC" TC1). *)

(* Locate negb. *)

(* Run TemplateProgram (TC1 <- Translate bool_TC "negb" ;; *)
(*                           tmDefinition "negb_TC" TC1). *)


(* Run TemplateProgram (TC1 <- Translate Ft_TC "covers" ;; *)
(*                           tmDefinition "covers_TC" TC1). *)

  
(*                                   (forall (f : F) *)
(*                                      (A : covers f -> Type) (B : Type) (s : forall u : (covers f), A u ≅ B), *)
(*                                       Σ (B' : Type) (s' : B' ≅ B), (forall u : (covers f), A u = B'))). *)






(* Print Ft_TC. *)

(* Print Iᵗ. *)
(* Print Forcing_I.orᵗ. *)
(* Print orᵗ. *)
(* Print Forcing_I.Iᵗ_obligation_1. *)

Definition dec (ϕ : Prop) : Prop := {ϕ} + {~ ϕ}.

Lemma dec_case_true {ϕ : Prop}  (H : ϕ) (Hdec : dec ϕ) : Hdec = left H.
  destruct Hdec.
  f_equal. apply proof_irr.
  destruct (n H).
Defined.

Lemma dec_case_false {ϕ : Prop}  (H : ~ ϕ) (Hdec : dec ϕ) : Hdec = right H.
  destruct Hdec.
  destruct (H ϕ0).
  apply proof_irr.
Defined.

  
Run TemplateProgram (tImplementTC isEq_TC "adm_TC" "adm"
                                  (Prop -> Prop)).
Next Obligation.
  exact (dec  (X p0 α p0 id)). (** could change that in many ways **)
Defined.


Run TemplateProgram (TC <- Translate adm_TC "iff" ;; 
                     tmDefinition "iff_TC" TC).




Run TemplateProgram (tImplementTC iff_TC "natp_TC" "natp"
                                  (Prop -> Prop)).
Next Obligation.
  exact (forall q β, X p0 α p0 id -> X q (β ô α) q id).
Defined.



Run TemplateProgram (tImplementTC natp_TC "adm_iff_TC" "adm_iff"
                                  (forall ϕ ψ : Prop, (ϕ <-> ψ) -> adm ϕ -> natp ϕ -> natp ψ -> adm ψ)).
Next Obligation.
  unfold admᵗ.
  unfold admᵗ_obligation_1.
  unfold iffᵗ in H. specialize (H p id).
  destruct H. simpl_comp_hyp.
  unfold admᵗ in H0.
  unfold admᵗ_obligation_1 in H0.
  specialize (H0 p id).
  destruct H0.
  - simpl_comp.
    specialize (H p id).
    left. apply H.
    intros. simpl_comp.
    unfold natpᵗ, natpᵗ_obligation_1 in H1.
    specialize (H1 p id p0 α).
    exact (H1 ϕ0).
  - right.
    intro. apply n. simpl_comp. simpl_comp_hyp. specialize (H3 p id).
    apply H3. intros. simpl_comp. simpl_comp_hyp.
    unfold natpᵗ, natpᵗ_obligation_1 in H2.
    specialize (H2 _ id _ α). exact (H2 H0).
Defined.
    

Run TemplateProgram (tImplementTC adm_iff_TC "Fforall_TC" "Fforall" ((I -> Prop) -> Prop)).
Next Obligation.
  exact (forall (k : 1 ~> p), X p id (fun p1 (β : p ~> p1) => (β ô k)) p0 α).
Defined.


(* Run TemplateProgram (tImplementTC Fforall_TC "Fforall_natp_TC" "Fforall_natp" *)
(*                                   (forall ϕ : I -> Prop, (forall i : I, natp (ϕ i)) -> natp (Fforall ϕ))). *)
(* Next Obligation. *)
(*   unfold natpᵗ, natpᵗ_obligation_1. *)
(*   unfold natpᵗ, natpᵗ_obligation_1  in H. *)
(*   unfold Fforallᵗ, Fforallᵗ_obligation_1. *)
(*   intros. simpl_comp. simpl_comp_hyp. *)
(*   specialize (H p id). simpl_comp_hyp.  *)
(*   specialize (H (fun p1 β0 => β0 ô k)). *)

Run TemplateProgram(tImplementTC Fforall_TC "Fforall_correct_1_TC" "Fforall_correct_1"
                                 (forall (ϕ : I -> Prop), (forall i : I, ϕ i) -> Fforall ϕ)).
Next Obligation.
  intros.
  simpl_comp. simpl_comp_hyp.
  unfold Fforallᵗ. unfold Fforallᵗ_obligation_1.
  intros. specialize (H p id (fun p1 β => β ô k)).
  simpl_comp. simpl_comp_hyp. simpl in H. exact H.
Defined.


Run TemplateProgram(tImplementTC Fforall_correct_1_TC "Fforall_correct_2_TC" "Fforall_correct_2"
                                 (forall (ϕ : I -> Prop), Fforall ϕ ->  (forall i : I, nati i -> ϕ i))).
Next Obligation.
  intros. simpl_comp.
  simpl_comp_hyp.
  unfold Fforallᵗ in H. unfold Fforallᵗ_obligation_1 in H.
  specialize (H p id). simpl_comp_hyp.
  unfold natiᵗ in H0. unfold Forcing_I.natiᵗ_obligation_1 in H0.
  specialize (H0 _ id). simpl_comp_hyp.
  assert ((fun p0 α => α ô i p id) = (fun (p0 : nat) (α : p ~> p0) => i p0 (α ô id)) ).
  { apply funext_dep. intro p0. apply funext_dep. intro α. rewrite H0. reflexivity. }
  destruct H1. specialize (H (i p id)). exact H.
Defined.


Fixpoint arrow_to_vector {p : nat} : (1 ~> p) -> Vector.t bool (Nat.pow 2 p).
  destruct p; unfold arrow.
  - intro. simpl. apply Vector.cons.
    + apply H.
      * intros [k Hk]. easy.
      * exact (zero_finset 0).
    + apply Vector.nil.
  - intro. simpl. apply Vector.append.
    + apply arrow_to_vector.
      intro x. apply H. intros [k Hk]. destruct (lt_eq_lt_dec k p) as [[H1|H1]|H1].
      * exact (x (exist _ k H1)).
      * exact true.
      * easy.
    + refine (Vector.append _ (Vector.nil _)).
      apply arrow_to_vector.
      intro x. apply H. intros [k Hk]. destruct (lt_eq_lt_dec k p) as [[H1|H1]|H1].
      * exact (x (exist _ k H1)).
      * exact false.
      * easy.
Defined.

Fixpoint proj1 {T : Type} {a b : nat}  (v : Vector.t T (a + b)) : Vector.t T a.
  destruct a.
  - apply Vector.nil.
  - simpl in v. Check Vector.caseS. destruct v using (Vector.caseS').
    apply Vector.cons. exact h. exact (proj1 T a b v).
Defined.

Fixpoint proj2 {T : Type} {a b : nat}  (v : Vector.t T (a + b)) : Vector.t T b.
  destruct a.
  - exact v.
  - simpl in v. destruct v using Vector.caseS'.
    exact (proj2 T a b v).
Defined.

Lemma append_proj {T : Type} {a b : nat}  (v : Vector.t T (a + b)) :
  Vector.append (proj1 v) (proj2 v) = v.
Proof.
  induction a.
  - reflexivity.
  - simpl in v. destruct v using Vector.caseS'. simpl. rewrite (IHa v). reflexivity.
Defined.

Lemma proj1_append {T : Type} {a b : nat}  (v : Vector.t T a) (v' : Vector.t T b) : proj1 (Vector.append v v') = v.
Proof.
  induction a.
  - simpl. destruct v using Vector.case0. reflexivity.
  - destruct v using Vector.caseS'.
    simpl. f_equal. apply IHa.
Defined.

Lemma proj2_append {T : Type} {a b : nat}  (v : Vector.t T a) (v' : Vector.t T b) : proj2 (Vector.append v v') = v'.
Proof.
  induction a.
  - destruct v using Vector.case0. reflexivity. 
  - destruct v using Vector.caseS'.
    simpl. apply IHa.
Defined.


Lemma eq_condition {T : Type} {a b : nat}  (v v': Vector.t T (a+ b)) : proj1 v = proj1 v' -> proj2 v = proj2 v' -> v = v'.
  intros.
  rewrite <- (append_proj v), <- (append_proj v'). destruct H, H0. reflexivity.
Defined.

Fixpoint vector_to_arrow {p : nat} (v : Vector.t bool (Nat.pow 2 p)) (x : cube p) {struct p}: (cube 1).
  destruct p.
  -  simpl in *. destruct v using Vector.caseS'. intro k. exact h. 
  - simpl in v.
    remember (x (last_finset p)) as xp. clear Heqxp. destruct xp.
    + apply (vector_to_arrow p (proj1 v) (degen_c (last_finset p) x)).
    + apply (vector_to_arrow p (proj1 (proj2 v)) (degen_c (last_finset p) x)).
Defined.

 Transparent degen_c.

Lemma arrow_to_arrow {p : nat} (c : 1 ~> p) : vector_to_arrow (arrow_to_vector c) = c.
Proof.
  induction p.
  - apply funext. intro x. apply funext. intro b. simpl.
    match goal with
    | |- c ?x' ?k' = _ => assert (x' = x)
    end.
    { apply funext. intros [x0 Hx0]. easy.
    }
    destruct H. f_equal.
    destruct b. unfold zero_finset.
    destruct (lt_eq_lt_dec x 0) as [[H|H]|H]; try easy.
    subst x. repeat f_equal. apply (Peano_dec.le_unique).
  - apply funext. intro x.
    apply funext. intro b.
    remember (x (last_finset p)) as xp. destruct xp.
    + simpl. rewrite <- Heqxp. simpl.
      rewrite proj1_append. rewrite IHp.
      match goal with
      | |- c ?x' ?k' = _ => assert (x' = x)
      end.
      { apply funext. intros [k Hk].
        destruct (lt_eq_lt_dec k p) as [[H|H]|H].
        * unfold degen_c. repeat f_equal. apply Peano_dec.le_unique.
        * rewrite Heqxp. unfold last_finset. subst k. repeat f_equal. apply Peano_dec.le_unique.
        * easy.
      }
      rewrite H. reflexivity.
    + simpl. rewrite <- Heqxp. simpl.
      rewrite proj2_append. rewrite proj1_append. rewrite IHp.
      match goal with
      | |- c ?x' ?k' = _ => assert (x' = x)
      end.
      { apply funext. intros [k Hk].
        destruct (lt_eq_lt_dec k p) as [[H|H]|H].
        * repeat f_equal. apply Peano_dec.le_unique.
        * rewrite Heqxp. unfold last_finset. subst k. repeat f_equal. apply Peano_dec.le_unique.
        * easy.
      }
      rewrite H. reflexivity.
Defined.


Lemma vector_to_vector {p : nat}  (v : Vector.t bool (Nat.pow 2 p)) : arrow_to_vector (vector_to_arrow v) = v.
Proof.
  induction p.
  - simpl in v. simpl.
    destruct v using Vector.caseS'.
    simpl. destruct v using Vector.case0.
    reflexivity.
  - simpl in v.
    apply eq_condition.
    + simpl.
      rewrite proj1_append.
      refine (trans _ (IHp (proj1 v))).
      apply f_equal.
      apply funext. intro x.
      destruct (lt_eq_lt_dec p p) as [[H|H]|H]; try easy.
      simpl. apply funext. intro b. simpl.
      f_equal. apply funext.
      intros [k Hk]. clear H.
      destruct (lt_eq_lt_dec k p) as [[H|H]|H].
      * repeat f_equal. apply Peano_dec.le_unique.
      * easy.
      * easy.
    + apply eq_condition.
      * simpl.
        rewrite proj2_append.
        rewrite proj1_append.
        refine (trans _ (IHp (proj1 (proj2 v)))).
        apply f_equal.
        apply funext. intro x.
        destruct (lt_eq_lt_dec p p) as [[H|H]|H]; try easy.
        simpl. apply funext. intro b. simpl.
        f_equal. apply funext.
        intros [k Hk]. clear H.
        destruct (lt_eq_lt_dec k p) as [[H|H]|H].
        -- repeat f_equal. apply Peano_dec.le_unique.
        -- easy.
        -- easy.
      * match goal with
        | |- ?x = ?y => generalize x; generalize y
        end.
        intros t t0. destruct t using Vector.case0.
        destruct t0 using Vector.case0. reflexivity.
Defined.

Fixpoint list_all n : list (Vector.t bool n).
Proof.
  destruct n.
  - refine ([Vector.nil _]).
  - remember (list_all n) as list_all_n.
    apply app.
    + refine (map _ list_all_n).
      apply Vector.cons. exact true.
    + refine (map _ list_all_n).
      apply Vector.cons. exact false.
Defined.
  
Inductive appears_in {T : Type} (x : T) : list T -> Prop :=
  app_now  (l : list T) : appears_in x (x :: l)
| app_later (y : T) (l : list T) : appears_in x l -> appears_in x (y :: l).


Lemma appears_in_left {T : Type} (x : T) (l1 l2 : list T) : appears_in x l1 -> appears_in x (l1 ++ l2).
Proof.
  intro H.
  induction H.
  - simpl. constructor.
  - simpl. constructor. assumption.
Defined.

Lemma appears_in_right {T : Type} (x : T) (l1 l2 : list T) : appears_in x l2 -> appears_in x (l1 ++ l2).
Proof.
  intro H.
  induction l1.
  -  simpl. assumption.
  - simpl; constructor; assumption.
Defined.
  
Lemma vector_bool_dec {n : nat} : forall x y : Vector.t bool n, {x = y} + {~(x=y)}.
Proof.
  intros x y.
  induction  x.
  - left. destruct y using Vector.case0. reflexivity.
  - destruct y using Vector.caseS'.
    destruct h, h0.
    + destruct (IHx y).
      * left.
        f_equal. exact e.
      * right.
        intro. apply Vector.cons_inj in H. destruct H. exact (n0 H0).
    +  right.
       intro. apply Vector.cons_inj in H. destruct H. inversion H.
    + right.
      intro. apply Vector.cons_inj in H. destruct H. inversion H.
    + destruct (IHx y).
      * left.
        f_equal. exact e.
      * right.
        intro. apply Vector.cons_inj in H. destruct H. exact (n0 H0).
Defined.


Lemma appears_map {T T' : Type} (f : T -> T') (x : T) (l : list T) : appears_in x l -> appears_in (f x) (map f l).
Proof.
  intro H.
  induction H.
  - simpl. constructor.
  - simpl. constructor. assumption.
Defined.
  

Lemma all_vector_appear {n : nat} : forall v : (Vector.t bool n), appears_in v (list_all n).
Proof.
  intro v; induction v.
  -  simpl. constructor.
  - simpl.
    destruct h.
    + apply appears_in_left.
      apply appears_map. exact IHv.
    + apply appears_in_right.
      apply appears_map. exact IHv.
Defined.


Fixpoint forall_dec_aux {p : nat} ( ϕ : 1 ~> p -> Prop) (Hϕ : forall x : 1 ~> p, dec (ϕ x)) (l : list (Vector.t bool (Nat.pow 2 p))) :
  {forall x : 1 ~> p, appears_in (arrow_to_vector x) l -> (ϕ x)} +
  {Σ x : 1 ~> p, appears_in (arrow_to_vector x) l /\ ~ (ϕ x)}.
Proof.
  destruct l.
  - left.
    intros x H.
    inversion H.
  - destruct (Hϕ (vector_to_arrow t)) as [Ha|Ha].
    + destruct (forall_dec_aux p ϕ Hϕ l) as [IHl|IHl].
      * left. intro x.
        intro H. destruct (vector_bool_dec  (arrow_to_vector x) t). subst t. rewrite arrow_to_arrow in Ha. exact Ha.
        remember (t :: l) as l'. destruct H. inversion Heql'. easy. inversion Heql'. clear Heql'. subst l0. subst y.
        exact (IHl x H).
      * right. destruct IHl.
        exists x. destruct a. split.
        -- constructor. assumption.
        -- assumption.
    + right. exists (vector_to_arrow t).
      split.
      * rewrite vector_to_vector. constructor.
      * assumption.
Defined.

Definition forall_dec {p : nat} ( ϕ : 1 ~> p -> Prop) (Hϕ : forall x : 1 ~> p, dec (ϕ x)) : dec (forall x, ϕ x).
Proof.
  destruct (forall_dec_aux ϕ Hϕ (list_all (Nat.pow 2 p))).
  - left. intro i. apply ϕ0. apply all_vector_appear.
  - right. intro. destruct s. destruct a. exact (H1 (H x)). 
Defined.

Run TemplateProgram (tImplementTC Fforall_correct_2_TC "Fforall_adm_TC" "Fforall_adm"
                                  (forall (ϕ : I -> Prop) (Hϕ : forall i : I, adm (ϕ i)),
                                     adm (Fforall ϕ))).
Next Obligation.
  unfold admᵗ. unfold admᵗ_obligation_1.
  unfold admᵗ in Hϕ. unfold admᵗ_obligation_1 in Hϕ.
  unfold Fforallᵗ. unfold Fforallᵗ_obligation_1. simpl_comp_hyp. simpl_comp.
  specialize (Hϕ p id). simpl_comp_hyp.
  apply forall_dec.
  intro k. specialize (Hϕ (fun p1 β => β ô k)). exact Hϕ.
Defined.
  
  
  
  



Run TemplateProgram (tImplementTC natp_TC "ax9_TC" "ax9"
                                  (forall (ϕ : Prop) (Hnat : natp ϕ) (Hcof : adm ϕ) 
                                     (A : ϕ -> Type) (B : Type) (s : forall u : ϕ, A u ≅ B),
                                      Σ (B' : Type) (s' : B' ≅ B), (forall u : ϕ, A u = B'))).
Next Obligation.
  unfold admᵗ, admᵗ_obligation_1 in Hcof; unfold dec in Hcof; unfold natpᵗ, natpᵗ_obligation_1 in Hnat.
   unshelve refine (existTᵗ _ _ _ _ _).
  (* Define B' *)
  - intros p0 α0 p1 α1.
    refine (sumbool_rect (fun X => _) _ _ (Hcof p0 α0)); intro c.
    + simpl_comp_hyp. eapply (A p0 α0).
      * intros p2 α2. simpl_comp. simpl_comp_hyp. specialize (Hnat p0 α0 p2 α2). simpl_comp_hyp.
        exact (Hnat c).
      * exact α1.
    + exact (B p0 α0 p1 α1).
  - intros p0 α0. unshelve refine (existTᵗ _ _ _ _ _).
    (* Prove B ≅ B' *)
    + intros p1 α1. unfold isEquivᵗ. unshelve refine (existTᵗ _ _ _ _ _).
      (* First direction of equivalence *)
      * intros p2 α2 HB'. simpl_comp. simpl_comp_hyp. 
        refine (sumbool_rect (fun X => _) _ _ (Hcof p2 (α2 ô α1 ô α0))) ; intro c.
        -- specialize (s p2 (α2 ô α1 ô α0)). simpl_comp_hyp.
           unshelve eassert (s := s _).
           { intros p3 α3. apply Hnat. exact c. }
           simpl in s. assert (g := projEq1' s).
           specialize (g p2 id). apply g. clear g.
           intros p3 α3. specialize (HB' p3 α3). clear s.
           assert (H := Hnat _ (α2 ô α1 ô α0) _ α3). simpl_comp_hyp.
           match goal with
           | [Hb' : sumbool_rect ?a1 ?a2 ?a3 (Hcof _ _) |- _ ] => 
             apply (transport (fun W => sumbool_rect a1 a2 a3 W) (dec_case_true (H c) (Hcof p3 (α3 ô α2 ô α1 ô α0)))) in HB'
           end.
           simpl in HB'. simpl.
           assert ((fun (p4 : nat) (α4 : p3 ~> p4) => Hnat p3 (α3 ô α2 ô α1 ô α0) p4 α4 (H c)) =
                    (fun (p4 : nat) (α : p3 ~> p4) => Hnat p2 (fun x : cube p2 => α0 ((α2 ô α1) x)) p4 (α ô (α3 ô id ô id)) c)) as Hpi.
           { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. }
           exact (transport (fun W => A p3 (α3 ô α2 ô α1 ô α0) W p3 id) Hpi HB'). 
        -- specialize (HB' p2 id).
           simpl_comp_hyp.
           rewrite (dec_case_false c (Hcof p2 (α2 ô α1 ô α0))) in HB'.
           simpl in HB'.
           exact HB'.
      * intros p2 α2. unshelve refine (existTᵗ _ _ _ _ _).
        (* Second direction of equivalence *)
        -- intros p3 α3 HB. simpl_comp. simpl_comp_hyp.
           match goal with
           | |- ?GG => refine (sumbool_rect (fun X => GG) _ _ (Hcof p3 (α3 ô α2 ô α1 ô α0))) ; intro c
           end.
           ++ rewrite (dec_case_true c (Hcof p3 _)). simpl.
              unshelve eassert (s := s p3 (α3 ô α2 ô α1 ô α0) _).
              { intros p4 α4. eapply Hnat. exact c. }
              pose (projEq2' s) as g. specialize (g p3 id). simpl in g. simpl_comp_hyp. apply g. exact HB.
           ++  rewrite (dec_case_false c (Hcof p3 _)). simpl.
               exact (HB p3 id).
        -- intros p3 α3. apply conjᵗ.
           (* First identity of equivalence *)
           ++ intros p4 α4. apply eq_is_eq.
              apply funext_dep. intro p5. apply funext_dep. intro α5.
              unfold fcomposeᵗ. apply funext_dep. intro b. simpl_comp.
              refine (sumbool_rect (fun X => _) _ _ (Hcof p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0))) ; intro c.
              ** simpl_comp_hyp. change (α5 ô (α4 ô α3) ô α2 ô α1 ô α0) with (α5 ô α4 ô α3 ô α2 ô α1 ô α0).
                 rewrite (dec_case_true c (Hcof p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0))).
                 simpl. etransitivity.
                 --- refine (f_equal _ _).
                     apply funext_dep. intro p6. apply funext_dep. intro α6. simpl_comp. simpl. 
                     change (α6 ô (α5 ô α4) ô α3 ô α2 ô α1 ô α0) with (α6 ô (α5 ô α4 ô α3 ô α2 ô α1 ô α0)).
                     assert (Hnat6 := Hnat _ (α5 ô α4 ô α3 ô α2 ô α1 ô α0) _ α6).
                     simpl_comp_hyp. specialize (Hnat6 c).
                     rewrite (dec_case_true Hnat6 (Hcof p6 (α6 ô (α5 ô α4 ô α3 ô α2 ô α1 ô α0)))).
                     (** should work with an explicit transport **)
                     
                     destruct (dec_case_true c (Hcof p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0))).
                     pose proof (sym (covering_assumption (restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))).
                 match goal with
                 | |- transport ?X2 ?X3 (transport ?X4 ?X5 (sumbool_rect ?X6 ?X7 ?X8 _)) = ?X1 =>
                   apply (transport (fun x => transport X2 X3 (transport X4 X5 (sumbool_rect X6 X7 X8 x)) = X1) H)
                 end. simpl. etransitivity.
                 refine (f_equal _ _). eapply (sym (transport_trans _ _ _ _)).
                 etransitivity. refine (f_equal _ _). apply transport_sym_trans. etransitivity.
                 refine (sym (transport_trans _ _ _ _)).
                 refine (transport_ap (fun x => (projEq2'
                                                (s p6 (id ô (id ô α6) ô (id ô α5 ô id) ô (id ô α4 ô id) ô α3 ô α2 ô α1 ô α0) x) p6 id
                                                (fun (p7 : nat) (α7 : p6 ~> p7) => b p7 (id ô α7 ô α6)))) _).
                 simpl.

                 pose ((s p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)
                          (fun (p6 : nat) (α6 : p5 ~> p6) =>
                             restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))) as ss.
                 pose proof (projEq3' ss p5 id) as Hs. inversion Hs. clear Hs.
                 unfold fcomposeᵗ in H0. unfold ss in H0.
                 apply apD10 with (x := p5) in H0. apply apD10 with (x := id) in H0.
                 apply apD10 with (x := b) in H0. simpl_comp.
                 (** * I think we need some kind of naturality for s, unless we somehow manage to call it with a higher forcing condition *)
                 rewrite <- H0. apply f_equal. apply funext_dep. intro p6. apply funext_dep. intro α6. simpl_comp. 
                 
                 destruct admitok.
              ** match goal with
                 | |- ?GG1 _ = b p5 id => apply (transport (fun x => GG1 x = b p5 id) (sym (noncovering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _).
                 match goal with
                 | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) (sym (noncovering_assumption c)))
                 end. simpl. reflexivity. etransitivity.
                 match goal with
                 | |- transport ?P1 ?E1 (transport ?P2 ?E2 ?X) = ?Y =>
                   exact (sym (transport_trans P1 E2 E1 X))
                 end. etransitivity. refine (transport_sym_trans _ _ _). reflexivity.
           (* Second identity of equivalence *)
           ++ intros p4 α4. apply eq_is_eq.
              apply funext_dep. intro p5. apply funext_dep. intro α5.
              unfold fcomposeᵗ. apply funext_dep. intro b'.
              refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)))) ; intro c.
              ** match goal with
                 | |- ?GG1 _ = b' p5 id => apply (transport (fun x => GG1 x = b' p5 id) (sym (covering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _). refine (f_equal _ _). refine (f_equal _ _).
                 apply funext_dep. intro p6. apply funext_dep. intro α6.
                 pose proof (sym (covering_assumption (restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))).
                 match goal with
                 | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) H)
                 end. simpl. reflexivity. etransitivity. refine (f_equal _ _). refine (f_equal _ _).
                 reflexivity.
                 (** * Same here *)
                 destruct admitok.
              ** match goal with
                 | |- ?GG1 _ = b' p5 id => apply (transport (fun x => GG1 x = b' p5 id) (sym (noncovering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _).
                 match goal with
                 | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) (sym (noncovering_assumption c)))
                 end. simpl. reflexivity. etransitivity.
                 match goal with
                 | |- transport ?P1 ?E1 (transport ?P2 ?E2 ?X) = ?Y =>
                   exact (sym (transport_trans P1 E2 E1 X))
                 end. etransitivity. refine (transport_trans_sym _ _ _).
                 reflexivity.
    (* Prove A u = B' *)
    + intros p1 α1. intro Hφ. apply eq_is_eq.
      apply funext_dep. intro p2. apply funext_dep. intro α2.
      apply funext_dep. intro p3. apply funext. intro α3. simpl.
      change (id ô (id ô α2 ô id) ô id ô (id ô α1 ô id) ô α0) with (α2 ô α1 ô α0). simpl_comp.
      destruct (covering_dec (f p2 (α2 ô α1 ô α0))).
      * assert ((fun (p5 : nat) (α4 : p2 ~> p5) => Hφ p5 (id ô α4 ô (id ô α2 ô id))) =
                (fun (p4 : nat) (α4 : p2 ~> p4) => restrict_covering (Hf p2 (α2 ô α1 ô α0) p4 α4) c)) as Hpi.
        { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. }
        simpl. refine (f_equal (fun x => A p2 _ x _ _) _). exact Hpi.
      * destruct (n (Hφ p2 α2)).
Defined. 


Run TemplateProgram (tImplementTC Ft_TC "ax9_TC" "ax9"
                                  (forall (f : F)
                                     (A : covers f -> Type) (B : Type) (s : forall u : (covers f), A u ≅ B),
                                      Σ (B' : Type) (s' : B' ≅ B), (forall u : (covers f), A u = B'))).
Next Obligation.
  unfold Fᵗ in f. unfold Fᵗ_obligation_1 in f.
  unshelve refine (existTᵗ _ _ _ _ _).
  (* Define B' *)
  - intros p0 α0 p1 α1.
    refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p0 α0))) ; intro c.
    + eapply (A p0 α0).
      * intros p2 α2. unfold coversᵗ. unfold coversᵗ_obligation_1.
        simpl_comp.
        eapply restrict_covering.
        -- specialize (Hf p0 α0 p2 α2). exact Hf.
        -- exact c.
      * exact α1.
    + exact (B p0 α0 p1 α1).
  - intros p0 α0. unshelve refine (existTᵗ _ _ _ _ _).
    (* Prove B ≅ B' *)
    + intros p1 α1. unfold isEquivᵗ. unshelve refine (existTᵗ _ _ _ _ _).
      (* First direction of equivalence *)
      * intros p2 α2 HB'.
        refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p2 (α2 ô α1 ô α0)))) ; intro c.
        -- specialize (s p2 (α2 ô α1 ô α0)).
           assert (forall (p3 : nat) (α3 : p2 ~> p3),
                      coversᵗ p3 (fun (p4 : nat) (α4 : p3 ~> p4) => f p4 (α4 ô α3 ô α2 ô α1 ô α0)) p3 id) as Hc'.
           { intros p3 α3. eapply restrict_covering.
             - exact (Hf p2 (α2 ô α1 ô α0) p3 α3).
             - exact c. }
           pose (projEq1' (s Hc')) as g. specialize (g p2 id). apply g.
           intros p3 α3. specialize (HB' p3 α3).
           apply (restrict_covering (Hf p2 (α2 ô α1 ô α0) p3 α3)) in c.
           assert ((fun (p4 : nat) (α4 : p3 ~> p4) => restrict_covering (Hf p3 (α3 ô α2 ô α1 ô α0) p4 α4) c) =
                   (fun (p4 : nat) (α4 : p3 ~> p4) => Hc' p4 (id ô α4 ô (α3 ô id)))) as Hpi.
           { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. }
           apply (transport _ (covering_assumption c)) in HB'. simpl in HB'.
           apply (transport (fun x => A p3 (α3 ô α2 ô α1 ô α0) x p3 id) Hpi) in HB'.
           exact HB'.
        -- specialize (HB' p2 id).
           apply (transport _ (noncovering_assumption c)) in HB'. simpl in HB'.
           exact HB'.
      * intros p2 α2. unshelve refine (existTᵗ _ _ _ _ _).
        (* Second direction of equivalence *)
        -- intros p3 α3 HB.
           match goal with
           | |- ?GG => refine (sumbool_rect (fun X => GG) _ _ (covering_dec (f p3 (α3 ô α2 ô α1 ô α0)))) ; intro c
           end.
           ++ apply (transport _ (sym (covering_assumption c))). simpl.
              assert (forall (p4 : nat) (α4 : p3 ~> p4),
                         coversᵗ p4 (fun (p5 : nat) (α5 : p4 ~> p5) => f p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)) p4 id) as Hc'.
              { intros p4 α4. eapply restrict_covering.
                - exact (Hf p3 (α3 ô α2 ô α1 ô α0) p4 α4).
                - exact c. }
              pose (projEq2' (s p3 (α3 ô α2 ô α1 ô α0) Hc')) as g. specialize (g p3 id). simpl in g.
              assert ((fun (p2 : nat) (α1 : p3 ~> p2) => Hc' p2 (id ô α1 ô id)) =
                      (fun (p4 : nat) (α4 : p3 ~> p4) => restrict_covering (Hf p3 (α3 ô α2 ô α1 ô α0) p4 α4) c)) as Hpi.
              { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. }
              refine (transport (fun x => A p3 (α3 ô α2 ô α1 ô α0) x _ _) Hpi _). apply g.
              intros p4 α4.
              exact (HB p4 α4).
           ++ apply (transport _ (sym (noncovering_assumption c))). simpl.
              exact (HB p3 id).
        -- intros p3 α3. apply conjᵗ.
           (* First identity of equivalence *)
           ++ intros p4 α4. apply eq_is_eq.
              apply funext_dep. intro p5. apply funext_dep. intro α5.
              unfold fcomposeᵗ. apply funext_dep. intro b.
              refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)))) ; intro c.
              ** match goal with
                 | |- ?GG1 _ = b p5 id => apply (transport (fun x => GG1 x = b p5 id) (sym (covering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _).
                 apply funext_dep. intro p6. apply funext_dep. intro α6.
                 pose proof (sym (covering_assumption (restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))).
                 match goal with
                 | |- transport ?X2 ?X3 (transport ?X4 ?X5 (sumbool_rect ?X6 ?X7 ?X8 _)) = ?X1 =>
                   apply (transport (fun x => transport X2 X3 (transport X4 X5 (sumbool_rect X6 X7 X8 x)) = X1) H)
                 end. simpl. etransitivity.
                 refine (f_equal _ _). eapply (sym (transport_trans _ _ _ _)).
                 etransitivity. refine (f_equal _ _). apply transport_sym_trans. etransitivity.
                 refine (sym (transport_trans _ _ _ _)).
                 refine (transport_ap (fun x => (projEq2'
                                                (s p6 (id ô (id ô α6) ô (id ô α5 ô id) ô (id ô α4 ô id) ô α3 ô α2 ô α1 ô α0) x) p6 id
                                                (fun (p7 : nat) (α7 : p6 ~> p7) => b p7 (id ô α7 ô α6)))) _).
                 simpl.

                 pose ((s p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)
                          (fun (p6 : nat) (α6 : p5 ~> p6) =>
                             restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))) as ss.
                 pose proof (projEq3' ss p5 id) as Hs. inversion Hs. clear Hs.
                 unfold fcomposeᵗ in H0. unfold ss in H0.
                 apply apD10 with (x := p5) in H0. apply apD10 with (x := id) in H0.
                 apply apD10 with (x := b) in H0. simpl_comp.
                 (** * I think we need some kind of naturality for s, unless we somehow manage to call it with a higher forcing condition *)
                 rewrite <- H0. apply f_equal. apply funext_dep. intro p6. apply funext_dep. intro α6. simpl_comp. 
                 
                 destruct admitok.
              ** match goal with
                 | |- ?GG1 _ = b p5 id => apply (transport (fun x => GG1 x = b p5 id) (sym (noncovering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _).
                 match goal with
                 | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) (sym (noncovering_assumption c)))
                 end. simpl. reflexivity. etransitivity.
                 match goal with
                 | |- transport ?P1 ?E1 (transport ?P2 ?E2 ?X) = ?Y =>
                   exact (sym (transport_trans P1 E2 E1 X))
                 end. etransitivity. refine (transport_sym_trans _ _ _). reflexivity.
           (* Second identity of equivalence *)
           ++ intros p4 α4. apply eq_is_eq.
              apply funext_dep. intro p5. apply funext_dep. intro α5.
              unfold fcomposeᵗ. apply funext_dep. intro b'.
              refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)))) ; intro c.
              ** match goal with
                 | |- ?GG1 _ = b' p5 id => apply (transport (fun x => GG1 x = b' p5 id) (sym (covering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _). refine (f_equal _ _). refine (f_equal _ _).
                 apply funext_dep. intro p6. apply funext_dep. intro α6.
                 pose proof (sym (covering_assumption (restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))).
                 match goal with
                 | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) H)
                 end. simpl. reflexivity. etransitivity. refine (f_equal _ _). refine (f_equal _ _).
                 reflexivity.
                 (** * Same here *)
                 destruct admitok.
              ** match goal with
                 | |- ?GG1 _ = b' p5 id => apply (transport (fun x => GG1 x = b' p5 id) (sym (noncovering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _).
                 match goal with
                 | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) (sym (noncovering_assumption c)))
                 end. simpl. reflexivity. etransitivity.
                 match goal with
                 | |- transport ?P1 ?E1 (transport ?P2 ?E2 ?X) = ?Y =>
                   exact (sym (transport_trans P1 E2 E1 X))
                 end. etransitivity. refine (transport_trans_sym _ _ _).
                 reflexivity.
    (* Prove A u = B' *)
    + intros p1 α1. intro Hφ. apply eq_is_eq.
      apply funext_dep. intro p2. apply funext_dep. intro α2.
      apply funext_dep. intro p3. apply funext. intro α3. simpl.
      change (id ô (id ô α2 ô id) ô id ô (id ô α1 ô id) ô α0) with (α2 ô α1 ô α0). simpl_comp.
      destruct (covering_dec (f p2 (α2 ô α1 ô α0))).
      * assert ((fun (p5 : nat) (α4 : p2 ~> p5) => Hφ p5 (id ô α4 ô (id ô α2 ô id))) =
                (fun (p4 : nat) (α4 : p2 ~> p4) => restrict_covering (Hf p2 (α2 ô α1 ô α0) p4 α4) c)) as Hpi.
        { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. }
        simpl. refine (f_equal (fun x => A p2 _ x _ _) _). exact Hpi.
      * destruct (n (Hφ p2 α2)).
Defined. 