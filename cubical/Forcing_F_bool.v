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




Definition last_finset (n : nat) : finset (S n).
  exists n. easy.
Defined.

Definition finset_inj (n : nat) : finset n -> finset (S n).
  intros [m p]. exists m. apply le_S. exact p.
Defined.

Definition face_lattice  := bool.


Definition join_faces : face_lattice  -> face_lattice  -> face_lattice  := orb.



    

Definition meet_faces  (f1 : face_lattice ) : face_lattice  -> face_lattice  := andb f1.



Definition covering  (f : face_lattice ) : Prop :=
  match f with
  |true => True
  |false => False
  end.



Theorem covering_join (f g : face_lattice ) :
  covering (join_faces f g) <-> covering f \/ covering g.
Proof.
  split; intro H; destruct f.
  - left. reflexivity.
  - destruct g.
    + right. reflexivity.
    + inversion H.
  - reflexivity.
  - destruct g.
    + reflexivity.
    + destruct H as [H | H]; inversion H.
Defined.





Theorem covering_meet  (f g : face_lattice) :
  covering (meet_faces f g) <-> covering f /\ covering g.
Proof.
  split; intro H; destruct f.
  - destruct g.
    + split; reflexivity.
    + inversion H.
  - inversion H.
  - destruct g.
    + reflexivity.
    + destruct H as [H H']; inversion H'.
  - destruct H as [H H']. inversion H.
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


Fixpoint empty_forall_covering_in_list_dec {p : nat} ( f : 1 ~> p -> face_lattice) (l : list (Vector.t bool (Nat.pow 2 p))) :
  {forall x : 1 ~> p, appears_in (arrow_to_vector x) l -> covering (f x)} +
  {(exists x : 1 ~> p, appears_in (arrow_to_vector x) l /\ ~ covering (f x))}.
Proof.
  destruct l.
  - left.
    intros x H.
    inversion H.
  - remember (f (vector_to_arrow t)) as ft. destruct (ft).
    + destruct (empty_forall_covering_in_list_dec p f l) as [IHl|IHl].
      * left. intro x.
        intro H. destruct (vector_bool_dec  (arrow_to_vector x) t). subst t.
        rewrite arrow_to_arrow in Heqft. symmetry in Heqft. rewrite Heqft. constructor.
        remember (t :: l) as l'. destruct H. inversion Heql'. easy. inversion Heql'. clear Heql'. subst l0. subst y.
        exact (IHl x H).
      * right. destruct IHl.
        exists x. destruct H. split.
        -- constructor. assumption.
        -- assumption.
    + right. exists (vector_to_arrow t).
      split.
      * rewrite vector_to_vector. constructor.
      * rewrite <- Heqft. unfold covering. intro. inversion H.
Defined.
  

Proposition forall_covering_dec {p : nat} (f : 1 ~> p ->  face_lattice)  :
  {forall i : 1 ~> p, covering (f i)} +  {~ (forall i : 1 ~> p, covering (f i))}.
Proof.
  destruct (empty_forall_covering_in_list_dec f (list_all (Nat.pow 2 p))).
  - left. intro i. apply c. apply all_vector_appear.
  - right. intro H. destruct e.
    destruct H0.
    specialize (H x). exact (H1 H).
Defined.


                                                       
Definition forall_faces {n : nat} (f : 1 ~> n -> face_lattice) : face_lattice.
  destruct (forall_covering_dec f). exact true. exact false.
Defined.
  

Theorem forall_faces_covering {n : nat} (f : 1 ~> n -> face_lattice) : covering (forall_faces f) <-> forall i : 1 ~> n, covering (f i).
  split.
  - intros H i.
    unfold forall_faces in H. destruct (forall_covering_dec f).
    + exact (c i).
    + inversion H.
  - intro H. unfold forall_faces.  destruct (forall_covering_dec f).
    + reflexivity. 
    + specialize (n0 H). inversion n0.  
Defined.

    
    

(* Should I setoid ? Should I SProp *)

Run TemplateProgram (tImplementTC ax4_TC "F_TC" "F" Type).
Next Obligation.
  exact (bool).
Defined.



Definition restricts  (f1 : face_lattice)  (f2 : face_lattice) :=
  match f1,f2 with
  | true, false => False
  | _,_ => True
  end. 
                         
Theorem restrict_covering  {f1 : face_lattice} {f2 : face_lattice}
        (H : restricts f1 f2)
  : covering f1 -> covering f2.
Proof.
  intros. destruct f1.
  - unfold restricts in H. simpl in H. exact H.
  - inversion H0.
Defined.

    


  
  

Lemma restrict_join  (f : face_lattice )  (g1 g2: face_lattice) :
  restricts f  g1 \/ restricts f  g2 -> restricts f  (join_faces g1 g2).
Proof.
  destruct f, g1, g2; intros; destruct H; try auto; try inversion H.
Defined.

Lemma restrict_join'  (f1 f2 : face_lattice)  (g: face_lattice) :
  restricts f1 g /\ restricts f2 g -> restricts (join_faces f1 f2) g.
Proof.
  destruct f1, f2, g; intros; destruct H; try auto.
Defined.

Lemma restrict_meet (f : face_lattice) (g1 g2: face_lattice ) :
  restricts f  g1 /\ restricts f  g2 -> restricts f  (meet_faces g1 g2).
Proof.
  destruct f, g1, g2; intro H; destruct H; try auto.
Defined.

Lemma restrict_meet'  (f1 f2 : face_lattice ) (g: face_lattice ) :
  restricts f1  g \/ restricts f2  g -> restricts (meet_faces f1 f2)  g.
Proof.
  destruct f1, f2, g; intros; destruct H; try auto; try inversion H.
Defined.


Lemma restrict_forall {q : nat} (f : face_lattice ) (g: 1 ~> q -> face_lattice ) :
  (forall i : 1 ~> q, restricts f  (g i)) -> restricts f  ( forall_faces g).
Proof.
  intro  H.
  unfold forall_faces. destruct f.
  - destruct (forall_covering_dec g).
    + easy.
    + assert (False).
      apply n. intro i. specialize (H i). easy.
      inversion H0.
  - easy.
Defined.

Lemma restrict_forall' {p : nat} (f : (1 ~> p) -> face_lattice )  (g:  face_lattice ) :
  (exists i : 1 ~> p, restricts (f i)  g) -> restricts (forall_faces f)  g.
Proof.
  intro  H. destruct H.
  unfold forall_faces.
  destruct (forall_covering_dec f).
  - destruct g.
    + easy.
    + specialize (c x). destruct (f x).
      * inversion H.
      * inversion c.
  - easy.
Defined.
 


Run TemplateProgram (tImplementTC F_TC "natf_TC" "natf" (F -> Prop)).
Next Obligation.
  rename X into f. rename α into α0.
  exact (forall (p1 : nat) (α1 : p0 ~> p1), restricts (f p0 α0) (f p1 (α1 ô α0))).
Defined.


 

Run TemplateProgram (tImplementTC natf_TC "covers_TC" "covers" (F -> Prop)).
Next Obligation.
  rename α into α0. rename X into f.
  exact (covering (f p0 α0)).
Defined.



Run TemplateProgram (tImplementTC covers_TC "realize_TC" "realize" (F -> Prop)).
Next Obligation.
  unfold Fᵗ, Fᵗ_obligation_1, face_lattice in X.
  rename X into f.
  specialize (f p0 α). exact (covering f). (* the problem is probably with this one, should give more constraint *)
Defined.



Definition sieve_equiv {p : nat} (S1 S2 : forall q : nat, p ~> q -> Prop) :=
  forall (q : nat) (α : p ~> q), S1 q α <-> S2 q α.

Notation "S ≈ T" := (sieve_equiv S T) (at level 65, left associativity).

(** Cofibrant propositions *)

(* Run TemplateProgram (tImplementTC realize_TC "cof_TC" "cof" (Prop -> Prop)). *)
(* Next Obligation. *)
(*   rename X into S. *)
(*   specialize (S p id). *)
(*   exact (exists f : (forall p0 : nat, p ~> p0 -> Fᵗ p0 p0 id), *)
(*             (fun (p0 : nat) (α : p ~> p0) => covering (f p0 α)) ≈ S). (** Why not cof Prop -> Type? **) *)
(* Defined. *)

(* (* this one seems a better definition. However, i need to put it in the translation database, and i dont *)
(*  know how to do this without dirty hacks. Also, I need sigma-types translation. *) *)
(* Definition cof' : Prop -> Prop := fun s => exists f : F, s = realize f. *)


Definition destruct_eq {p : nat} (f g : cube (S p) -> cube 1) :
  (f = g) <-> (forall b : bool, (f o face_c (last_finset p) b) =  (g o face_c (last_finset p) b)).
  split.
  - intro H. destruct H. reflexivity.
  - intro H. apply funext. intro d. remember (d (last_finset p)) as dp.
    specialize (H dp).
    assert ((face_c (last_finset p) dp) (degen_c (last_finset p) d) = d).
    + apply funext. intros [x Hx]. simpl. destruct (lt_eq_lt_dec x p) as [[H1 | H1] | H1].
      * repeat f_equal. apply Peano_dec.le_unique.
      * destruct H1. symmetry in Heqdp. destruct Heqdp. unfold last_finset. repeat f_equal. apply  Peano_dec.le_unique.
      * easy.
    + destruct H0.
      match goal with
      | |- context [f (face_c (last_finset p) dp ?x)] => change (f (face_c (last_finset p) dp x)) with ((f o face_c (last_finset p) dp) x)
      end.
      rewrite H.
      reflexivity.
Defined.

Fixpoint eq_decidable_cube {p : nat} (f g : cube p -> cube 1) {struct p}: {f = g} + { exists x k,  ~ (f x k = g x k)}.
  destruct p.
  - unfold cube in *. remember (f (fun _ => true) (zero_finset 0)) as f0.
    remember (g (fun _ => true) (zero_finset 0)) as g0.
    destruct f0, g0.
    + left. apply funext. intro x. apply funext. intro y.
      assert ((fun _ => true) = x). apply funext. intros [b Hb]. easy. destruct H.
      assert (zero_finset 0 = y). destruct y. destruct x. unfold zero_finset. f_equal. apply Peano_dec.le_unique. easy. destruct H.
      destruct Heqf0. destruct Heqg0. reflexivity.
    + right.
      exists (fun _ : finset 0 => true). exists (zero_finset 0). destruct Heqf0, Heqg0. easy.
    + right.
      exists (fun _ : finset 0 => true). exists (zero_finset 0). destruct Heqf0, Heqg0. easy.
    + left. apply funext. intro x. apply funext. intro y.
      assert ((fun _ => true) = x). apply funext. intros [b Hb]. easy. destruct H.
      assert (zero_finset 0 = y). destruct y. destruct x. unfold zero_finset. f_equal. apply Peano_dec.le_unique. easy. destruct H.
      destruct Heqf0. destruct Heqg0. reflexivity.
  - remember (f o face_c (last_finset p) true) as ftrue.
    remember (f o face_c (last_finset p) false) as ffalse.
    remember (g o face_c (last_finset p) true) as gtrue.
    remember (g o face_c (last_finset p) false) as gfalse.
    assert (eqtrue := eq_decidable_cube p ftrue gtrue).
    assert (eqfalse := eq_decidable_cube p ffalse gfalse).
    destruct eqtrue.
    * destruct eqfalse.
      -- destruct e, e0. left.
         apply destruct_eq. intro b. destruct b.
         rewrite <- Heqgtrue. rewrite <- Heqftrue. reflexivity.
         rewrite <- Heqgfalse. rewrite <- Heqffalse. reflexivity.
      -- right. destruct e. destruct e0. rewrite Heqffalse, Heqgfalse in H. destruct H.
         unfold fcompose in H. exists (face_c (last_finset p) false x).
         exists x0. exact H.
    * right. destruct e. destruct H. rewrite Heqftrue, Heqgtrue in H.
      unfold fcompose in H. exists (face_c (last_finset p) true x). exists x0. exact H.
Defined.




(** Since equality between i : cube p -> cube 1 is decidable, we define 
extremity i b := if i = I_end_map p b then None else false. 
Presumably this is not a good idea? **)

Definition extremity {p : nat} (b : bool) (i : cube p -> cube 1) : face_lattice.
  destruct (eq_decidable_cube i (I_end_map p b)). exact true. exact false.
Defined.
  

Theorem extremity_correct {p : nat} (b : bool) (i : cube p -> cube 1) :
  covering (extremity b i) <-> I_end_map p b = i.
Proof.
  unfold extremity. destruct ( eq_decidable_cube i (I_end_map p b)); split.
  - intro H. rewrite e. reflexivity.
  - intro H. reflexivity. 
  - intro H. inversion H. 
  - intro H. destruct e. destruct H0. symmetry in H.
    apply (TFUtils.ap (fun F => F x x0)) in H. easy.
Defined.




Run TemplateProgram (tImplementTC realize_TC "extremity_F0_TC" "F0" (forall (i : I), F)).
Next Obligation.
  unfold Fᵗ, Fᵗ_obligation_1. exact (extremity false (i p id)).
Defined.


Run TemplateProgram (tImplementTC extremity_F0_TC "natf_F0_TC" "natf_F0" (forall i : I, nati i -> natf (F0 i))).
Next Obligation.
  unfold natfᵗ, natfᵗ_obligation_1.
  intros. unfold F0ᵗ, F0ᵗ_obligation_1. 
  simpl_comp. unfold extremity. unfold natiᵗ, Forcing_I.natiᵗ_obligation_1 in H.
    specialize (H p id p1 α1). simpl_comp_hyp. rewrite <- H. 
    destruct (eq_decidable_cube (i p id) (I_end_map p false)).
  - simpl. 
    destruct (eq_decidable_cube (α1 ô i p id) (I_end_map p1 false)).
    + easy.
    + rewrite e in e0. destruct e0. destruct H0.  unfold compose, fcompose, I_end_map in H0. easy.
  - easy.
Defined.

Run TemplateProgram (TC <- Translate natf_F0_TC "iff" ;; 
                     tmDefinition "iff_TC" TC).

Run TemplateProgram (tImplementTC iff_TC "F0_correct_TC" "F0_correct" (forall (i : I), realize (F0 i) <-> (i = I0))).
Next Obligation.
  split.
  - intros. apply eq_is_eq. apply funext_dep. intro p1. apply funext_dep. intro α1. simpl_comp.
    unfold realizeᵗ, realizeᵗ_obligation_1 in H.
    unfold F0ᵗ, F0ᵗ_obligation_1 in H. specialize (H p1 α1).
    simpl_comp_hyp. rewrite extremity_correct in H. easy.
  - intros. simpl_comp. simpl_comp_hyp. specialize (H p0 id). 
    unfold realizeᵗ, realizeᵗ_obligation_1. 
    unfold F0ᵗ, F0ᵗ_obligation_1. apply extremity_correct. unfold I0ᵗ, Forcing_I.I0ᵗ_obligation_1 in H. unfold I_end in H.
    change (I_end_map p0 false) with ((fun (p : nat) (_ : p0 ~> p) => I_end_map p false) p0 id). destruct H. reflexivity.
Defined.



Definition realize_dec (f : F) := (realize f) \/ (~ realize f).



Run TemplateProgram (TC <- Translate F0_correct_TC "not" ;;
                        tmDefinition "not_TC" TC).

Run TemplateProgram (TC <- Translate not_TC "realize_dec" ;;
                        tmDefinition "real_dec_TC" TC).

(* Run TemplateProgram (tImplementTC real_dec_TC "natf_real_dec_TC" "natf_real_dec" (forall f : F, natf f -> realize_dec f)). *)
(* Next Obligation. *)
(*   unfold realize_decᵗ. specialize (H p id). unfold natfᵗ, natfᵗ_obligation_1 in H. simpl_comp; simpl_comp_hyp. *)
(*   remember (f p id) as fp. destruct (f p id). *)
(*   - left. *)
(*     intros. simpl_comp. unfold realizeᵗ, realizeᵗ_obligation_1. simpl_comp. specialize ( H p0 α). apply restrict_covering in H. *)
(*     apply H. rewrite Heqfp. easy. *)
(*   - right. *)
(*     intros. unfold notᵗ. intros. specialize (H0 p0 id). simpl_comp_hyp. *)
(*     unfold realizeᵗ, realizeᵗ_obligation_1 in H0. *)
    



(* Run TemplateProgram (tImplementTC F0_correct_TC "join_simon_TC" "join_simon" (forall A (φ φ' : F) *)
(*            (f : realize φ -> A) (g : realize φ' -> A) (H : forall u v, f u = g v),  realize φ \/ realize φ' -> A)). *)
(* Next Obligation. *)
(*   simpl_comp. simpl_comp_hyp. *)
(*   specialize (H0 p id). destruct H0. *)
(*   - remember (f p id) as fp. simpl_comp_hyp. apply fp. exact H0. *)
(*   - remember (g p id) as gp. simpl_comp_hyp. apply gp. exact H0. *)
(* Defined. *)

(* Definition left_or A B (x : A) :  A \/ B := or_introl x. *)

(* Run TemplateProgram (TC <- ImplementExisting join_simon_TC "left_or" ;; *)
(*                         tmDefinition "or_introl_TC" TC). *)
(* Next Obligation. *)
(*   apply or_introlᵗ. exact x. *)
(* Defined. *)

(* Run TemplateProgram (tImplementTC join_simon_TC "join_l_TC" "join_l" *)
(*                                   (forall {A} {φ φ' : F} (f : realize φ -> A) (g : realize φ' -> A) (H : forall u v, f u = g v) (u : realize φ), *)
(*                                       join_simon A φ φ' f g H (left_or _ _ u) = f u)). *)


(* Run TemplateProgram (tImplementTC real_dec_TC "test_TC" "test" (forall f : F, natf f ->  realize_dec f)). *)
(* Next Obligation. *)
(*   unfold realize_decᵗ. unfold realizeᵗ, realizeᵗ_obligation_1. simpl_comp. *)
(*   unfold extremity. unfold  natiᵗ, natiᵗ_obligation_1 in H. *)
(*   destruct (covering_dec (f p id)). *)
(*   - apply or_introlᵗ. intros. simpl_comp. *)
(*     specialize (H p id p0 α). simpl_comp_hyp. unfold natfᵗ, natfᵗ_obligation_1 in H. exact (restrict_covering H c). *)
(*   - apply or_introrᵗ. intros. simpl_comp. *)
(*     unfold natfᵗ, natfᵗ_obligation_1 in H. *)
(*     unfold notᵗ. intro. *)
(*     simpl_comp_hyp. *)
(*     (**** Impossible ??***) *)
(*  Admitted. *)

    

(* Run TemplateProgram (tImplementTC real_dec_TC "test_TC" "test" (forall i : I, nati i ->  realize_dec (F0 i))). *)
(* Next Obligation. *)
(*   unfold realize_decᵗ. unfold realizeᵗ, realizeᵗ_obligation_1. simpl_comp. unfold F0ᵗ. unfold F0ᵗ_obligation_1. *)
(*   unfold extremity. unfold  natiᵗ, natiᵗ_obligation_1 in H. *)
(*   destruct (eq_decidable_cube (i p id) (I_end_map p false)). *)
(*   - apply or_introrᵗ. intros. simpl_comp. *)
(*     specialize (H p id p0 α). *)
(*     simpl_comp_hyp. rewrite <- H. *)
(*     destruct (eq_decidable_cube (α ô i p id) (I_end_map p0 false)). *)
(*     + simpl. left. intro k. reflexivity. *)
(*     + destruct e0. destruct H0. rewrite e in H0. unfold fcompose, compose, I_end_map in H0. easy. *)
(*   - apply or_introlᵗ. unfold notᵗ. intros. simpl_comp_hyp. destruct e. destruct H1. *)
(*     specialize (H0 p0 id). simpl_comp_hyp. *)
(*     destruct (eq_decidable_cube (i p0 α) (I_end_map p0 false)). *)
(*     + specialize (H p id p0 α). simpl_comp_hyp. *)
(*       rewrite <- H in e. unfold compose, fcompose in e. unfold Iᵗ, Iᵗ_obligation_1 in i. *)
(*     (**** Impossible ??***) *)
(* Admitted. *)


Run TemplateProgram (tImplementTC F0_correct_TC "F1_TC" "F1" (forall (i : I), F)).
Next Obligation.
  unfold Fᵗ, Fᵗ_obligation_1. exact (extremity true (i p id)).
Defined.



Run TemplateProgram (tImplementTC F1_TC "F1_correct_TC" "F1_correct" (forall (i : I), realize (F1 i) <-> (i = I1))).
Next Obligation.
  split; intros.
  - apply eq_is_eq. apply funext_dep. intro p1. apply funext_dep. intro α1. simpl_comp.
    unfold realizeᵗ, realizeᵗ_obligation_1 in H.
    unfold F1ᵗ, F1ᵗ_obligation_1 in H. specialize (H p1 α1).
    simpl_comp_hyp. rewrite extremity_correct in H. easy.
  - specialize (H p0 id). 
    unfold realizeᵗ, realizeᵗ_obligation_1. 
    unfold F1ᵗ, F1ᵗ_obligation_1. apply extremity_correct. unfold I1ᵗ, Forcing_I.I1ᵗ_obligation_1 in H. unfold I_end in H.
    change (I_end_map p0 true) with ((fun (p : nat) (_ : p0 ~> p) => I_end_map p true) p0 id). destruct H. reflexivity.
Defined.

Run TemplateProgram (tImplementTC F1_correct_TC "F1_natf_TC" "F1_natf" (forall i : I, nati i -> natf (F1 i))).
Next Obligation.
  unfold natfᵗ, natfᵗ_obligation_1.
  intros. unfold F1ᵗ, F1ᵗ_obligation_1.
  simpl_comp. unfold extremity. unfold natiᵗ, Forcing_I.natiᵗ_obligation_1 in H.
  specialize (H p id p1 α1). simpl_comp_hyp. rewrite <- H. 
  destruct (eq_decidable_cube (i p id) (I_end_map p true)).
  - simpl. 
    destruct (eq_decidable_cube (α1 ô i p id) (I_end_map p1 true)).
    + simpl. easy. 
    + rewrite e in e0. destruct e0. destruct H0.  unfold compose, fcompose, I_end_map in H0. easy.
  - easy.
Defined.




Run TemplateProgram (tImplementTC F1_correct_TC "For_TC" "For" (F -> F -> F)).
Next Obligation.
  exact (join_faces (X p id) (X0 p id)).
Defined.

Run TemplateProgram (tImplementTC For_TC "For_correct_TC" "For_correct"
                                  (forall f g : F, natf f -> natf g -> realize (For f g) <-> realize f \/ realize g)).
Next Obligation.
  split; intros.
  - unfold realizeᵗ, realizeᵗ_obligation_1 in *. unfold Forᵗ, Forᵗ_obligation_1 in H1.
    specialize (H1 p0 id). apply covering_join in H1. destruct H1.
    + apply or_introlᵗ. intros. simpl_comp. simpl_comp_hyp.
      unfold natfᵗ, natfᵗ_obligation_1 in H. refine (restrict_covering _ _).
      * exact (H p0 α p1 α0).
      * exact H1.
    + apply or_introrᵗ. intros. simpl_comp. simpl_comp_hyp. unfold natfᵗ, natfᵗ_obligation_1 in H0. refine (restrict_covering _ _).
      * exact (H0 p0 α p1 α0).
      * exact H1.
  -  unfold realizeᵗ, realizeᵗ_obligation_1 in *.
     unfold Forᵗ, Forᵗ_obligation_1. simpl_comp. simpl_comp_hyp.
     apply covering_join.  specialize (H1 p0 id). destruct H1.
     + apply or_introl. exact (H1 p0 id).
     + apply or_intror. exact (H1 p0 id).
Defined.


Run TemplateProgram (tImplementTC For_correct_TC "For_natf_TC" "For_natf" (forall f g : F, natf f -> natf g -> natf (For f g))).
Next Obligation.
  unfold natfᵗ, natfᵗ_obligation_1 in *. intros. unfold Forᵗ, Forᵗ_obligation_1. simpl. simpl_comp; simpl_comp_hyp.
  specialize (H p id p1 α1). specialize (H0 p id p1 α1). simpl_comp. simpl_comp_hyp.
  apply restrict_join'. apply conj; apply restrict_join; easy.
Defined.


Lemma test f1 f2 : join_faces f1 f2 = f1 \/ join_faces f1 f2 = f2.
  destruct f1. left. reflexivity.
  right. reflexivity.
Defined.

  
Run TemplateProgram (tImplementTC For_natf_TC "Fand_TC" "Fand" (F -> F -> F)).
Next Obligation.
  exact (meet_faces (X p id) (X0 p id)).
Defined.

Run TemplateProgram (tImplementTC Fand_TC "Fand_correct_TC" "Fand_correct" (forall f g : F, realize (Fand f g) <-> realize f /\ realize g)).
Next Obligation.
  split; intros.
  - unfold realizeᵗ, realizeᵗ_obligation_1 in *. unfold Fandᵗ, Fandᵗ_obligation_1 in H.
    apply conjᵗ; simpl_comp; simpl_comp_hyp.
    + intros. specialize (H p1 α0).
      apply covering_meet in H. destruct H. exact H.
    + intros. specialize (H p1 α0).
      apply covering_meet in H. destruct H. exact H0.
  -   unfold realizeᵗ, realizeᵗ_obligation_1 in *.
      unfold Fandᵗ, Fandᵗ_obligation_1. simpl_comp. simpl_comp_hyp.
      apply covering_meet. specialize (H p0 id). destruct H. apply conj. 
      +  exact (H p0 id).
      +  exact (H0 p0 id).
Defined.

Run TemplateProgram (tImplementTC Fand_correct_TC "Fand_natf_TC" "Fand_natf" (forall f g : F, natf f -> natf g -> natf (Fand f g))).
Next Obligation.
  unfold natfᵗ, natfᵗ_obligation_1 in *. intros. unfold Fandᵗ, Fandᵗ_obligation_1. simpl. simpl_comp; simpl_comp_hyp.
  specialize (H p id p1 α1). specialize (H0 p id p1 α1). simpl_comp. simpl_comp_hyp.
  apply restrict_meet. split; apply restrict_meet'.
  - left. exact H.
  - right. exact H0.
Defined.


Run TemplateProgram (tImplementTC Fand_natf_TC "Fforall_TC" "Fforall" ((I -> F) -> F)).
Next Obligation.
  specialize (X p id). apply (@forall_faces p). intro k. apply X. intros. unfold Iᵗ, Forcing_I.Iᵗ_obligation_1. exact (α ô k).
Defined.
 

Run TemplateProgram (tImplementTC Fforall_TC "Fforall_correct_TC" "Forall_correct"
                                  (forall f : I -> F, realize (Fforall f) <-> forall i : I, nati i -> realize (f i))).
Next Obligation.
  split.
  - intros.
    unfold realizeᵗ, realizeᵗ_obligation_1 in *. simpl_comp.
    specialize (H p0 id). simpl_comp_hyp. unfold Fforallᵗ, Fforallᵗ_obligation_1 in H.
    rewrite forall_faces_covering in H. simpl_comp_hyp.
    specialize (H (i p0 id)).
    unfold natiᵗ, Forcing_I.natiᵗ_obligation_1 in H0.
    assert ((fun (p1 : nat) (α0 : p0 ~> p1) => i p1 (α0 ô id)) = (fun (p1 : nat) (α : p0 ~> p1) => α ô i p0 id)).
    { apply funext_dep. intro p1. apply funext_dep. intro α1. simpl_comp.
      specialize (H0 _ id _ α1). simpl_comp_hyp. easy.
    } rewrite H1. exact H.
  - intros. unfold realizeᵗ, realizeᵗ_obligation_1 in *. simpl_comp. simpl_comp_hyp.
    unfold Fforallᵗ, Fforallᵗ_obligation_1. rewrite forall_faces_covering.
    intro i. specialize (H p0 id). simpl_comp_hyp. simpl_comp.
    match goal with
    | |- covering (f p0 α (fun p1 α0 => @?k p1 α0)) => specialize (H k)
    end.
    apply H.
    intros.
    unfold natiᵗ, Forcing_I.natiᵗ_obligation_1. reflexivity.
Defined.


Definition G := Σ (f : F), natf f.

Run TemplateProgram (TC1 <- Translate Fforall_correct_TC "G" ;;
                         tmDefinition "G_TC" TC1).


Run TemplateProgram (tImplementTC G_TC "FGforall_TC" "Gforall" ((I -> G) -> G)).
Next Obligation.
  specialize (X p id).
  unfold Gᵗ. 
  unshelve refine (existTᵗ _ _ _ _ _).
  - intros p0 α.
    apply (@forall_faces p). intro k.
    specialize (X (fun q j => j ô k)). unfold Gᵗ in X. destruct X. apply (x p id).
  - intros. unfold natfᵗ, natfᵗ_obligation_1.
    intros.
    apply restrict_forall.
    intro i. apply restrict_forall'.
    exists i. remember (X (fun q j => j ô i)) as Xi. destruct Xi.
    destruct (x p id); easy.
Defined.
 

(* Run TemplateProgram (tImplementTC Fforall_correct_TC "Fforall_natf_TC" "Fforall_natf" *)
(*                                   (forall f : I -> F, (forall i : I, natf (f i))  ->  natf (Fforall f ))). *)
(* Next Obligation. *)
(*   unfold natfᵗ, natfᵗ_obligation_1 in *. *)
(*   intros. *)
(*   unfold Fforallᵗ, Fforallᵗ_obligation_1. *)
(*   apply restrict_forall. *)
(*   intro i. *)
(*   apply restrict_forall'. *)
(*   simpl_comp; simpl_comp_hyp. *)
(*   specialize (H p id). simpl_comp_hyp. *)
(*   assert (1 ~> p). Focus 2. *)
(*   exists X. specialize (H (fun _ j => j ô X) p1 α1). simpl_comp. simpl_comp_hyp. simpl in H. *)
(*   (** This only works if we can find X such that α1 ô X = i. **) *)
(* Admitted. *)


Run TemplateProgram (tImplementTC G_TC "Fforall_JG_TC" "Fforall_JG" ((J -> G) -> G)).
Next Obligation.
  specialize (X p id).
  unfold Gᵗ. 
  unshelve refine (existTᵗ _ _ _ _ _).
  - intros p0 α.
    apply (@forall_faces p). intro k.
    assert (forall p0 : nat, p ~> p0 -> Jᵗ p0 p0 id).
    { intros.
      unfold Jᵗ.
      unshelve refine (existTᵗ _ _ _ _ _).
      + intros. exact (α0 ô X0 ô k).
      + intros. unfold natiᵗ, Forcing_I.natiᵗ_obligation_1.
        intros. reflexivity.
    }
    specialize (X X0).
    unfold Gᵗ in X. destruct X. apply (x p id).
  - intros. unfold natfᵗ, natfᵗ_obligation_1.
    intros.
    apply restrict_forall.
    intro i. apply restrict_forall'.
    exists i. simpl.
    match goal with
    | |- context[ X ?arg ] => remember arg as Xarg
    end.
    destruct (X Xarg). destruct (x p id); easy.
Defined.


Run TemplateProgram (tImplementTC Fforall_JG_TC "realize_G_TC" "realize_G" (G -> Prop)).
Next Obligation.
  unfold Gᵗ in X. specialize (X p id).
  destruct X. clear n. specialize (x p0 α).
  exact (covering x). (* the problem is probably with this one, should give more constraint *)
Defined.

 

(* Run TemplateProgram (tImplementTC realize_G_TC "Fforall_correct_TC" "Forall_correct" *)
(*                                   (forall f : J -> G, realize_G (Fforall_JG f) <-> forall i : J, realize_G (f i))). *)
(* Next Obligation. *)
(*   split. *)
(*   - intros. *)
(*     unfold realize_Gᵗ, realize_Gᵗ_obligation_1 in *. simpl_comp. *)
(*     specialize (H p0 id). simpl_comp_hyp. unfold Fforall_JGᵗ, Fforall_JGᵗ_obligation_1 in H. *)
(*     rewrite forall_faces_covering in H. simpl_comp_hyp. *)
(*     remember (i p0 id) as ip0. *)
(*     destruct ip0. specialize (H (x p0 id)). *)
(*     match goal with *)
(*     | H : covering match f p0 α ?arg1 with | _ => _ end |- *)
(*       match f p0 α ?arg2 with | _ => _ end => assert (arg1 = arg2) *)
(*     end. *)
(*     { apply funext_dep. intro p1. apply funext_dep. intro α1. simpl_comp. *)
(*       unfold natjᵗ, Forcing_I.natjᵗ_obligation_1 in H0. specialize (H0 p0 id p1 α1). simpl_comp_hyp. rewrite H0. *)
(*       unshelve refine (dep_eq _ _ _ _ _ _). *)
(*       +  apply funext_dep. intro p2. apply funext_dep. intro α0. rewrite <- Heqip0. unfold natiᵗ, Forcing_I.natiᵗ_obligation_1 in n. *)
(*          clear Heqip0. *)
(*          specialize (n _ id _ α1). simpl_comp_hyp. rewrite <- n. reflexivity. *)
(*       + simpl.  apply funext_dep. intro p2. apply funext_dep. intro α0. *)
(*         rewrite <- Heqip0. simpl. apply funext_dep. intro p3. apply funext_dep. intro α2. *)
(*         generalize (n p0 id p1 α1). intro e. simpl_comp_hyp. destruct e. simpl. *)
(*         match goal with *)
(*         | |- transport _ ?e _ _ _ _ _ = _ => assert (e = eq_refl) *)
(*         end. *)
(*         { *)
(*           match goal with *)
(*           | |- funext_dep _ _ (fun p4 => @?e p4 ) = eq_refl => assert ((fun p4 => e p4) = (fun p4 => eq_refl)) *)
(*           end. *)
(*           { apply funext_dep. intro p4. apply funext_dep_refl. } *)
(*           rewrite H1. apply funext_dep_refl. } *)
(*         rewrite H1. simpl. reflexivity. } *)
(*     destruct H1. *)
(*     match goal with *)
(*     | |- context [f p0 α ?arg] => destruct (f p0 α arg) *)
(*     end. *)
(*     exact H. *)
(*   - intros. unfold realize_Gᵗ, realize_Gᵗ_obligation_1 in *. simpl_comp. simpl_comp_hyp. *)
(*     unfold Fforall_JGᵗ, Fforall_JGᵗ_obligation_1. rewrite forall_faces_covering. *)
(*     intro i. specialize (H p0 id). simpl_comp_hyp. simpl_comp. *)
(*     match goal with *)
(*     | |- context [f p0 α (fun p1 X0 => @?arg p1 X0)] => specialize (H arg) *)
(*     end. *)
(*     match goal with *)
(*     | H : ?t -> _  |- _ => assert t *)
(*     end. *)
(*     { *)
(*       intros. unfold natjᵗ, Forcing_I.natjᵗ_obligation_1. *)
(*       intros. reflexivity. } *)
(*     specialize (H H0). clear H0. simpl_comp_hyp. simpl in H. simpl_comp_hyp. *)
(*     match goal with *)
(*     | H : match f p0 α ?arg1 with | _ => _ end |- *)
(*       covering match f p0 α ?arg2 with | _ => _ end => assert (arg1 = arg2) *)
(*     end. *)
(*     { *)
(*       repeat (apply funext_dep; intro). simpl_comp. reflexivity. *)
(*     } destruct H0. *)
(*     match goal with *)
(*     | |- context [f p0 α ?arg] => destruct (f p0 α arg) *)
(*     end. *)
(*     exact H. *)
(* Defined. *)
      
                         

(* (* Run TemplateProgram (tImplementTC ax5_TC "ax6_TC" "ax6" (forall ϕ ψ : Prop, cof ϕ -> cof ψ -> cof (ϕ /\ ψ))). *) *)
(* (* Next Obligation. *) *)


(* (* (* unshelve refine (ex_intro _ _ _). specialize (H p id). specialize (H0 p id).  *) *) *)
(* (*   (* - intros p0 α0. unfold cofᵗ in H, H0. unfold cofᵗ_obligation_1 in H, H0. simpl_comp_hyp. *) *) *)
(* (* Admitted. *) *)




(* Definition isEquiv (A B : Type) : Type := *)
(*   Σ (f : A -> B) (g : B -> A), (f o g = fun x => x) /\ (g o f = fun x => x). *)

(* Notation "A ≅ B" := (isEquiv A B) (at level 65, left associativity). *)

(* Run TemplateProgram (TC1 <-  Translate Fforall_correct_TC "fcompose" ;; *)
(*                           TC2 <-  Translate TC1 "isEquiv" ;; *)
(*                          tmDefinition "isEq_TC" TC2). *)

(* Definition projEq1' {p : nat} *)
(*            {A B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id} *)
(*   : isEquivᵗ p A B p id -> *)
(*     (forall (p0 : nat) (α : p ~> p0), *)
(*         (forall (p1 : nat) (α0 : p0 ~> p1), *)
(*             A p1 (α0 ô α) p1 id) -> B p0 α p0 id *)
(*     ). *)
(*   intros [x _]. exact x. *)
(* Defined. *)

(* Definition projEq2' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id} *)
(*            {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id} *)
(*   : isEquivᵗ p A B p id -> (forall (p0 : nat) (α : p ~> p0), *)
(*                               (forall (p1 : nat) (α0 : p0 ~> p1), B p1 (α0 ô α) p1 id) -> *)
(*                               A p0 α p0 id). *)
(*   intros [x y]. destruct (y p id) as [z _]. exact z. *)
(* Defined. *)

(* Definition projEq3' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id} *)
(*            {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id} *)
(*            (ie : isEquivᵗ p A B p id) *)
(*            : (forall (p0 : 𝐂_obj) (α : p ~> p0), *)
(*                  eqᵗ p0 *)
(*                      (fun (p1 : nat) (α0 : p0 ~> p1) (p2 : nat) (α1 : p1 ~> p2) => *)
(*                         (forall (p3 : nat) (α2 : p2 ~> p3), *)
(*                             B p3 (α2 ô α1 ô α0 ô α) p3 id) -> *)
(*                         B p2 (α1 ô α0 ô α) p2 id) *)
(*                      (fun (p1 : nat) (α0 : p0 ~> p1) => *)
(*                         fcomposeᵗ p1 *)
(*                                   (fun (p2 : nat) (α1 : p1 ~> p2) => *)
(*                                      B p2 (α1 ô α0 ô α)) *)
(*                                   (fun (p2 : nat) (α1 : p1 ~> p2) => *)
(*                                      A p2 (α1 ô α0 ô α)) *)
(*                                   (fun (p2 : nat) (α1 : p1 ~> p2) => *)
(*                                      B p2 (α1 ô α0 ô α)) *)
(*                                   (fun (p2 : nat) (α1 : p1 ~> p2) => projEq1' ie p2 (α1 ô α0 ô α)) *)
(*                                   (fun (p2 : nat) (α1 : p1 ~> p2) => projEq2' ie p2 (α1 ô α0 ô α))) *)
(*                      (fun (p1 : nat) (α0 : p0 ~> p1) *)
(*                         (x : forall (p2 : nat) (α1 : p1 ~> p2), *)
(*                             B p2 (α1 ô α0 ô α) p2 id) => *)
(*                         x p1 id)). *)
(*   destruct ie as [x y]. simpl. *)
(*   destruct (y p id) as [z t]. destruct (t p id) as [a b]. *)
(*   exact a. *)
(* Defined. *)

(* Definition projEq4' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id} *)
(*            {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id} *)
(*            (ie : isEquivᵗ p A B p id) *)
(*            : (forall (p0 : 𝐂_obj) (α : p ~> p0), *)
(*                  eqᵗ p0 *)
(*                      (fun (p1 : nat) (α0 : p0 ~> p1) (p2 : nat) (α1 : p1 ~> p2) => *)
(*                         (forall (p3 : nat) (α2 : p2 ~> p3), *)
(*                             A p3 (α2 ô α1 ô α0 ô α) p3 id) -> *)
(*                         A p2 (α1 ô α0 ô α) p2 id) *)
(*                      (fun (p1 : nat) (α0 : p0 ~> p1) => *)
(*                         fcomposeᵗ p1 *)
(*                                   (fun (p2 : nat) (α1 : p1 ~> p2) => *)
(*                                      A p2 (α1 ô α0 ô α)) *)
(*                                   (fun (p2 : nat) (α1 : p1 ~> p2) => *)
(*                                      B p2 (α1 ô α0 ô α)) *)
(*                                   (fun (p2 : nat) (α1 : p1 ~> p2) => *)
(*                                      A p2 (α1 ô α0 ô α)) *)
(*                                   (fun (p2 : nat) (α1 : p1 ~> p2) => projEq2' ie p2 (α1 ô α0 ô α)) *)
(*                                   (fun (p2 : nat) (α1 : p1 ~> p2) => projEq1' ie p2 (α1 ô α0 ô α))) *)
(*                      (fun (p1 : nat) (α0 : p0 ~> p1) *)
(*                         (x : forall (p2 : nat) (α1 : p1 ~> p2), *)
(*                             A p2 (α1 ô α0 ô α) p2 id) => *)
(*                         x p1 id)). *)
(*   destruct ie as [x y]. simpl. destruct (y p id) as [z t]. destruct (t p id) as [a b]. exact b. *)
(* Defined. *)

(* Definition covering_dec {p : nat} (f : face_lattice p) : {covering f} + {~ covering f}. *)
(* Proof. *)
(*   destruct f. *)
(*   -  left. easy. *)
(*   - right. easy. *)
(* Defined. *)

(* Theorem covering_assumption {p : nat} {f : face_lattice p} (c : covering f) : covering_dec f = left c. *)
(* Proof. *)
(*   unfold covering_dec. destruct f. *)
(*   - apply f_equal. apply proof_irr. *)
(*   - inversion c.  *)
(* Qed. *)

(* Theorem noncovering_assumption {p : nat} {f : face_lattice p} (c : ~ covering f) : covering_dec f = right c. *)
(* Proof. *)
(*   unfold covering_dec. destruct f. *)
(*   - assert (False). apply c. easy. inversion H. *)
(*   - apply f_equal. apply proof_irr. *)
(* Qed. *)



(* Run TemplateProgram (tImplementTC isEq_TC "ax9_TC" "ax9" *)
(*                                   (forall (f : F) (Hf : natf f) *)
(*                                      (A : covers f -> Type) (B : Type) (s : forall u : (covers f), A u ≅ B), *)
(*                                       Σ (B' : Type) (s' : B' ≅ B), (forall u : (covers f), A u = B'))). *)
(* Next Obligation. *)
(*   unfold Fᵗ in f. unfold Fᵗ_obligation_1 in f. *)
(*   unshelve refine (existTᵗ _ _ _ _ _). *)
(*   (* Define B' *) *)
(*   - intros p0 α0 p1 α1. *)
(*     refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p0 α0))) ; intro c. *)
(*     + eapply (A p0 α0). *)
(*       * intros p2 α2. unfold coversᵗ. unfold coversᵗ_obligation_1. *)
(*         simpl_comp. *)
(*         eapply restrict_covering. *)
(*         -- specialize (Hf p0 α0 p2 α2). exact Hf. *)
(*         -- exact c. *)
(*       * exact α1. *)
(*     + exact (B p0 α0 p1 α1). *)
(*   - intros p0 α0. unshelve refine (existTᵗ _ _ _ _ _). *)
(*     (* Prove B ≅ B' *) *)
(*     + intros p1 α1. unfold isEquivᵗ. unshelve refine (existTᵗ _ _ _ _ _). *)
(*       (* First direction of equivalence *) *)
(*       * intros p2 α2 HB'. *)
(*         refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p2 (α2 ô α1 ô α0)))) ; intro c. *)
(*         -- specialize (s p2 (α2 ô α1 ô α0)). *)
(*            assert (forall (p3 : nat) (α3 : p2 ~> p3), *)
(*                       coversᵗ p3 (fun (p4 : nat) (α4 : p3 ~> p4) => f p4 (α4 ô α3 ô α2 ô α1 ô α0)) p3 id) as Hc'. *)
(*            { intros p3 α3. eapply restrict_covering. *)
(*              - exact (Hf p2 (α2 ô α1 ô α0) p3 α3). *)
(*              - exact c. } *)
(*            pose (projEq1' (s Hc')) as g. specialize (g p2 id). apply g. *)
(*            intros p3 α3. specialize (HB' p3 α3). *)
(*            apply (restrict_covering (Hf p2 (α2 ô α1 ô α0) p3 α3)) in c. *)
(*            assert ((fun (p4 : nat) (α4 : p3 ~> p4) => restrict_covering (Hf p3 (α3 ô α2 ô α1 ô α0) p4 α4) c) = *)
(*                    (fun (p4 : nat) (α4 : p3 ~> p4) => Hc' p4 (id ô α4 ô (α3 ô id)))) as Hpi. *)
(*            { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. } *)
(*            apply (transport _ (covering_assumption c)) in HB'. simpl in HB'. *)
(*            apply (transport (fun x => A p3 (α3 ô α2 ô α1 ô α0) x p3 id) Hpi) in HB'. *)
(*            exact HB'. *)
(*         -- specialize (HB' p2 id). *)
(*            apply (transport _ (noncovering_assumption c)) in HB'. simpl in HB'. *)
(*            exact HB'. *)
(*       * intros p2 α2. unshelve refine (existTᵗ _ _ _ _ _). *)
(*         (* Second direction of equivalence *) *)
(*         -- intros p3 α3 HB. *)
(*            match goal with *)
(*            | |- ?GG => refine (sumbool_rect (fun X => GG) _ _ (covering_dec (f p3 (α3 ô α2 ô α1 ô α0)))) ; intro c *)
(*            end. *)
(*            ++ apply (transport _ (sym (covering_assumption c))). simpl. *)
(*               assert (forall (p4 : nat) (α4 : p3 ~> p4), *)
(*                          coversᵗ p4 (fun (p5 : nat) (α5 : p4 ~> p5) => f p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)) p4 id) as Hc'. *)
(*               { intros p4 α4. eapply restrict_covering. *)
(*                 - exact (Hf p3 (α3 ô α2 ô α1 ô α0) p4 α4). *)
(*                 - exact c. } *)
(*               pose (projEq2' (s p3 (α3 ô α2 ô α1 ô α0) Hc')) as g. specialize (g p3 id). simpl in g. *)
(*               assert ((fun (p2 : nat) (α1 : p3 ~> p2) => Hc' p2 (id ô α1 ô id)) = *)
(*                       (fun (p4 : nat) (α4 : p3 ~> p4) => restrict_covering (Hf p3 (α3 ô α2 ô α1 ô α0) p4 α4) c)) as Hpi. *)
(*               { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. } *)
(*               refine (transport (fun x => A p3 (α3 ô α2 ô α1 ô α0) x _ _) Hpi _). apply g. *)
(*               intros p4 α4. *)
(*               exact (HB p4 α4). *)
(*            ++ apply (transport _ (sym (noncovering_assumption c))). simpl. *)
(*               exact (HB p3 id). *)
(*         -- intros p3 α3. apply conjᵗ. *)
(*            (* First identity of equivalence *) *)
(*            ++ intros p4 α4. apply eq_is_eq. *)
(*               apply funext_dep. intro p5. apply funext_dep. intro α5. *)
(*               unfold fcomposeᵗ. apply funext_dep. intro b. *)
(*               refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)))) ; intro c. *)
(*               ** match goal with *)
(*                  | |- ?GG1 _ = b p5 id => apply (transport (fun x => GG1 x = b p5 id) (sym (covering_assumption c))) *)
(*                  end. simpl. etransitivity. refine (f_equal _ _). *)
(*                  apply funext_dep. intro p6. apply funext_dep. intro α6. *)
(*                  pose proof (sym (covering_assumption (restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))). *)
(*                  match goal with *)
(*                  | |- transport ?X2 ?X3 (transport ?X4 ?X5 (sumbool_rect ?X6 ?X7 ?X8 _)) = ?X1 => *)
(*                    apply (transport (fun x => transport X2 X3 (transport X4 X5 (sumbool_rect X6 X7 X8 x)) = X1) H) *)
(*                  end. simpl. etransitivity. *)
(*                  refine (f_equal _ _). eapply (sym (transport_trans _ _ _ _)). *)
(*                  etransitivity. refine (f_equal _ _). apply transport_sym_trans. etransitivity. *)
(*                  refine (sym (transport_trans _ _ _ _)). *)
(*                  refine (transport_ap (fun x => (projEq2' *)
(*                                                 (s p6 (id ô (id ô α6) ô (id ô α5 ô id) ô (id ô α4 ô id) ô α3 ô α2 ô α1 ô α0) x) p6 id *)
(*                                                 (fun (p7 : nat) (α7 : p6 ~> p7) => b p7 (id ô α7 ô α6)))) _). *)
(*                  simpl. *)

(*                  pose ((s p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) *)
(*                           (fun (p6 : nat) (α6 : p5 ~> p6) => *)
(*                              restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))) as ss. *)
(*                  pose proof (projEq3' ss p5 id) as Hs. inversion Hs. clear Hs. *)
(*                  unfold fcomposeᵗ in H0. unfold ss in H0. *)
(*                  apply apD10 with (x := p5) in H0. apply apD10 with (x := id) in H0. *)
(*                  apply apD10 with (x := b) in H0. simpl_comp. *)
(*                  (** * I think we need some kind of naturality for s, unless we somehow manage to call it with a higher forcing condition *) *)
(*                  rewrite <- H0. apply f_equal. apply funext_dep. intro p6. apply funext_dep. intro α6. simpl_comp.  *)
                 
(*                  destruct admitok. *)
(*               ** match goal with *)
(*                  | |- ?GG1 _ = b p5 id => apply (transport (fun x => GG1 x = b p5 id) (sym (noncovering_assumption c))) *)
(*                  end. simpl. etransitivity. refine (f_equal _ _). *)
(*                  match goal with *)
(*                  | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) (sym (noncovering_assumption c))) *)
(*                  end. simpl. reflexivity. etransitivity. *)
(*                  match goal with *)
(*                  | |- transport ?P1 ?E1 (transport ?P2 ?E2 ?X) = ?Y => *)
(*                    exact (sym (transport_trans P1 E2 E1 X)) *)
(*                  end. etransitivity. refine (transport_sym_trans _ _ _). reflexivity. *)
(*            (* Second identity of equivalence *) *)
(*            ++ intros p4 α4. apply eq_is_eq. *)
(*               apply funext_dep. intro p5. apply funext_dep. intro α5. *)
(*               unfold fcomposeᵗ. apply funext_dep. intro b'. *)
(*               refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)))) ; intro c. *)
(*               ** match goal with *)
(*                  | |- ?GG1 _ = b' p5 id => apply (transport (fun x => GG1 x = b' p5 id) (sym (covering_assumption c))) *)
(*                  end. simpl. etransitivity. refine (f_equal _ _). refine (f_equal _ _). refine (f_equal _ _). *)
(*                  apply funext_dep. intro p6. apply funext_dep. intro α6. *)
(*                  pose proof (sym (covering_assumption (restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))). *)
(*                  match goal with *)
(*                  | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) H) *)
(*                  end. simpl. reflexivity. etransitivity. refine (f_equal _ _). refine (f_equal _ _). *)
(*                  reflexivity. *)
(*                  (** * Same here *) *)
(*                  destruct admitok. *)
(*               ** match goal with *)
(*                  | |- ?GG1 _ = b' p5 id => apply (transport (fun x => GG1 x = b' p5 id) (sym (noncovering_assumption c))) *)
(*                  end. simpl. etransitivity. refine (f_equal _ _). *)
(*                  match goal with *)
(*                  | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) (sym (noncovering_assumption c))) *)
(*                  end. simpl. reflexivity. etransitivity. *)
(*                  match goal with *)
(*                  | |- transport ?P1 ?E1 (transport ?P2 ?E2 ?X) = ?Y => *)
(*                    exact (sym (transport_trans P1 E2 E1 X)) *)
(*                  end. etransitivity. refine (transport_trans_sym _ _ _). *)
(*                  reflexivity. *)
(*     (* Prove A u = B' *) *)
(*     + intros p1 α1. intro Hφ. apply eq_is_eq. *)
(*       apply funext_dep. intro p2. apply funext_dep. intro α2. *)
(*       apply funext_dep. intro p3. apply funext. intro α3. simpl. *)
(*       change (id ô (id ô α2 ô id) ô id ô (id ô α1 ô id) ô α0) with (α2 ô α1 ô α0). simpl_comp. *)
(*       destruct (covering_dec (f p2 (α2 ô α1 ô α0))). *)
(*       * assert ((fun (p5 : nat) (α4 : p2 ~> p5) => Hφ p5 (id ô α4 ô (id ô α2 ô id))) = *)
(*                 (fun (p4 : nat) (α4 : p2 ~> p4) => restrict_covering (Hf p2 (α2 ô α1 ô α0) p4 α4) c)) as Hpi. *)
(*         { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. } *)
(*         simpl. refine (f_equal (fun x => A p2 _ x _ _) _). exact Hpi. *)
(*       * destruct (n (Hφ p2 α2)). *)
(* Defined.  *)