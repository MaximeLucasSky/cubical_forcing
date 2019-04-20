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


Definition constraint (n : nat) := (finset n) -> (option bool).

Definition face_lattice (n : nat) := list (constraint n).


Definition join_faces {n : nat} : face_lattice n -> face_lattice n -> face_lattice n.
  intro f. induction f.
  - intro f'. exact f'.
  - intro f'. exact (a::(IHf f')).
Defined.

Definition meetable {n : nat} (c d : constraint n) :=
  forall k : finset n, forall b b', c k = Some b /\ d k = Some b' -> b = b'. 

Fixpoint meetable_dec {n : nat} (c d : constraint n) {struct n}: {meetable c d} + {exists k b, c k = Some b /\ d k = Some (negb b)}.
  destruct n.
  - left. unfold meetable. intros [k Hk]. easy.
  - destruct (meetable_dec n (c o (finset_inj n)) (d o (finset_inj n))).
    + remember (c (last_finset n)) as cn. remember (d (last_finset n)) as dn.
      destruct cn.
      * destruct dn.
        -- destruct b,b0.
           ++ left. unfold meetable. intros [k Hk] b b' [Hc Hd]. destruct (Compare_dec.lt_eq_lt_dec k n) as [[Hkn|Hkn]|Hkn].
              ** unfold meetable in m. specialize (m (exist _ k Hkn) b b'). apply m.
                 apply conj.
                 --- unfold fcompose. simpl. rewrite <- Hc. repeat f_equal. apply Peano_dec.le_unique.
                 --- unfold fcompose. simpl. rewrite <- Hd. repeat f_equal. apply Peano_dec.le_unique.
              ** destruct Hkn. unfold last_finset in *. assert ((PeanoNat.Nat.lt_succ_diag_r k) = Hk). apply Peano_dec.le_unique.
                 destruct H. destruct Heqcn. destruct Heqdn. inversion Hc. inversion Hd. reflexivity.
              ** easy.
           ++ right. exists (last_finset n). exists true. split; easy.
           ++ right. exists (last_finset n). exists false. split; easy.
           ++ left. unfold meetable. intros [k Hk] b b' [Hc Hd]. destruct (Compare_dec.lt_eq_lt_dec k n) as [[Hkn|Hkn]|Hkn].
              ** unfold meetable in m. specialize (m (exist _ k Hkn) b b'). apply m.
                 apply conj.
                 --- unfold fcompose. simpl. rewrite <- Hc. repeat f_equal. apply Peano_dec.le_unique.
                 --- unfold fcompose. simpl. rewrite <- Hd. repeat f_equal. apply Peano_dec.le_unique.
              ** destruct Hkn. unfold last_finset in *. assert ((PeanoNat.Nat.lt_succ_diag_r k) = Hk). apply Peano_dec.le_unique.
                 destruct H. destruct Heqcn. destruct Heqdn. inversion Hc. inversion Hd. reflexivity.
              ** easy.
        -- left. unfold meetable. intros [k Hk] b0 b0' [Hc Hd].
           destruct (Compare_dec.lt_eq_lt_dec k n) as [[Hkn|Hkn]|Hkn].
           ++ unfold meetable in m. specialize (m (exist _ k Hkn) b0 b0'). apply m.
              apply conj.
              ** unfold fcompose. simpl. rewrite <- Hc. repeat f_equal. apply Peano_dec.le_unique.
              ** unfold fcompose. simpl. rewrite <- Hd. repeat f_equal. apply Peano_dec.le_unique.
           ++ destruct Hkn. unfold last_finset in *.  assert ((PeanoNat.Nat.lt_succ_diag_r k) = Hk). apply Peano_dec.le_unique.
              destruct H. rewrite Hd in Heqdn. inversion Heqdn.
           ++ easy.
      * left. unfold meetable. intros [k Hk] b b' [Hc Hd].
        destruct (Compare_dec.lt_eq_lt_dec k n) as [[Hkn|Hkn]|Hkn].
        -- unfold meetable in m. specialize (m (exist _ k Hkn) b b'). apply m.
           apply conj.
           ++ unfold fcompose. simpl. rewrite <- Hc. repeat f_equal. apply Peano_dec.le_unique.
           ++ unfold fcompose. simpl. rewrite <- Hd. repeat f_equal. apply Peano_dec.le_unique.
        -- destruct Hkn. unfold last_finset in *.  assert ((PeanoNat.Nat.lt_succ_diag_r k) = Hk). apply Peano_dec.le_unique.
           destruct H. rewrite Hc in Heqcn. inversion Heqcn.
        -- easy.
    + right.
      destruct e as [[k Hk] [b [Hc Hd]]].
      assert (k < S n). easy. exists (exist _ k H). exists b.
      unfold finset_inj in *. unfold fcompose in *.
      split.
      -- destruct Hc. repeat f_equal. apply Peano_dec.le_unique.
      -- destruct Hd. repeat f_equal. apply Peano_dec.le_unique.
Defined.

Definition meet_constraint {n : nat} (c d : constraint n) : constraint n.
  intro k.
  remember (c k) as ck. remember (d k) as dk.
  destruct ck as [|].
  + exact (Some b).
  + exact dk.
Defined.

Lemma meet_constraint_comm {n : nat} (c d : constraint n) (H : meetable c d): meet_constraint c d = meet_constraint d c. 
Proof.
  unfold meet_constraint. destruct (meetable_dec c d).
  - apply funext. intro k. 
    remember (c k) as ck; remember (d k) as dk.
    destruct ck, dk.
    + unfold meetable in m. specialize (m k b b0). destruct Heqck, Heqdk.
      specialize (m (conj eq_refl eq_refl)). destruct m. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - destruct e as [k [b [Hc Hd]]]. unfold meetable in H.
    specialize (H k b (negb b) (conj Hc Hd)). destruct b; easy.
Defined.

    
(* Definition forall_constraint1 {n : nat} (c : (1 ~> n) -> constraint n) : constraint (S n). *)
(*   unfold arrow in *. *)
(*   intros  *)
(*   - exact (Some (fun _ => None)). *)
(*   - unfold arrow in *.  *)
(*   apply ax1 in c. *)
(*   destruct c as [c|]. *)
(*   - destruct n. *)
(*     + unfold constraint' in *. unfold constraint. apply Some. intros [k Hk]. easy. *)
(*     + destruct (c (last_finset n)). *)
(*       * exact None. *)
(*       * exact (Some c). *)
(*   - exact None. *)
(* Defined. *)

(* Definition degen_constraint {n : nat} (k : finset n) (c : constraint n) : constraint n. *)
(*   destruct (c k). *)
(*   - exact (fun _ => Some false). *)
(*   - exact c. *)
(* Defined. *)

Fixpoint meet_faces_aux {n : nat} (c : constraint n) (f : face_lattice n) : face_lattice n.
  destruct f.
  - exact nil.
  - destruct (meetable_dec c c0).
    + exact ((meet_constraint c c0) :: meet_faces_aux n c f).
    + exact (meet_faces_aux n c f).
Defined.

Fixpoint meet_faces {n : nat} (f1 : face_lattice n) : face_lattice n -> face_lattice n.
  destruct f1.
  - apply (fun _ => nil).
  - intro f2.
    exact (join_faces (meet_faces_aux c f2)  (meet_faces n f1 f2)).
Defined.

(* Definition forall_faces {n : nat} : face_lattice n -> face_lattice n := map (forall_constraint). *)
    
Definition empty_constraint {n : nat} : constraint n -> Prop.
  intros c. exact (forall m : finset n, c m = None).
Defined.


Fixpoint covering {n : nat} (f : face_lattice n) : Prop :=
  match f with
  | nil => False
  | c::tl => (empty_constraint c) \/ (covering tl)
  end.



Theorem covering_join {n : nat} (f g : face_lattice n) :
  covering (join_faces f g) <-> covering f \/ covering g.
Proof.
  revert g. induction f.
  - intro g. simpl. split.
    + intro H ; now right.
    + intros [H | H] ; easy.
  - intro g. simpl. split.
    + intros [H | H]. left ; now left. apply (IHf g) in H. destruct H. left ; now right. now right.
    + intros [[H | H] | H]. now left. right. apply (IHf g). now left. right. apply (IHf g). now right.
Qed.

(* Lemma covering_forall_constraint {n : nat} (c : constraint n) : *)
(*   empty_constraint (forall_constraint c) <-> empty_constraint c. *)
(* Proof. *)
(*   destruct c. *)
(*   - destruct n. *)
(*     + simpl. split. *)
(*       * intro H. unfold empty_constraint'. intros [k Hk]. easy. *)
(*       * intro H. intros [k Hk]. easy. *)
(*     + split. *)
(*       * simpl. intro H. unfold empty_constraint'. intros [k Hk]. remember (c (last_finset n)) as cn. destruct cn. *)
(*         -- simpl in H. destruct H. *)
(*         -- simpl in H. destruct (Compare_dec.lt_eq_lt_dec k n) as [[Hk'|Hk']|Hk']. *)
(*            ++ exact (H (exist _ k Hk)). *)
(*            ++ destruct Hk'. rewrite Heqcn. unfold last_finset. repeat f_equal. apply Peano_dec.le_unique. *)
(*            ++ easy. *)
(*       * intro H. simpl.  remember (c (last_finset n)) as cn. destruct cn. *)
(*         -- specialize (H (last_finset n)). destruct Heqcn. inversion H. *)
(*         -- exact H. *)
(*   - simpl. easy. *)
(* Defined. *)

Lemma covering_meet_constraint {n : nat} (c d : constraint n) (Hmeet : meetable c d):
  empty_constraint (meet_constraint c d) <-> empty_constraint c /\ empty_constraint d.
Proof.
  split; intro H.
  - unfold empty_constraint in *.
    split.
    + unfold meet_constraint in H.
      intro m.
      specialize (H m). simpl in H.
      destruct (c m) as [[|]|]; destruct (d m) as [[|]|]; try inversion H.
      reflexivity.
    + intro.
      specialize (H m).
      unfold meet_constraint in H. simpl in H.
      simpl in H. destruct (c m) as [[|]|]; destruct (d m) as [[|]|]; try inversion H.
      reflexivity.
  - simpl in *. destruct H as [Hc Hd]. unfold meet_constraint. 
    intro m.
    specialize (Hc m). specialize (Hd m).
    rewrite  Hc. exact Hd.
Defined.


Lemma covering_meet_faces_aux {n : nat} (c : constraint n) (f : face_lattice n) :
  covering (meet_faces_aux c f) <-> empty_constraint c /\ covering f.
Proof.
  - split;
    induction f.
    + intro H. simpl in H. contradiction.
    + simpl. intro H. destruct (meetable_dec c a).
      * simpl in H. destruct H; split.
        -- simpl in H. rewrite covering_meet_constraint in H. exact (proj1 H). exact m.
        -- rewrite covering_meet_constraint in H. exact (or_introl (proj2 H)). exact m.
        -- apply IHf in H. exact (proj1 H).
        -- apply IHf in H. exact (or_intror (proj2 H)).
      * split.
        -- exact (proj1 (IHf H)).
        -- right. exact (proj2 (IHf H)).
    + simpl. intro H. exact (proj2 H).
    + simpl. intro H. destruct (meetable_dec c a).
      * destruct H. destruct H0.
        -- refine (or_introl _). apply covering_meet_constraint. exact m. exact (conj H H0).
        -- refine (or_intror _). apply IHf. exact (conj H H0).
      * apply IHf. destruct H. destruct H0.
        -- destruct e as [k [b [Hc Ha]]]. specialize (H k). rewrite H in Hc. easy.
        -- exact (conj H H0).
Defined.



Theorem covering_meet {n : nat} (f g : face_lattice n) :
  covering (meet_faces f g) <-> covering f /\ covering g.
Proof.
  induction f.
  - simpl. split.
    + intro. contradiction.
    + intro. destruct H. contradiction.
  - simpl. split.
     + intro. apply covering_join in H. destruct H.
       *  apply covering_meet_faces_aux in H. exact (conj (or_introl (proj1 H)) (proj2 H)).
       * apply IHf in H. exact (conj (or_intror (proj1 H)) (proj2 H)).
     + intro H.  apply covering_join. destruct H. destruct H.
       * apply or_introl. apply covering_meet_faces_aux. exact (conj H H0).
       * apply or_intror. apply IHf. exact (conj H H0).
Defined.

(* Theorem covering_forall  {n : nat} (f : face_lattice n) : *)
(*   covering (forall_faces f) <-> covering f. *)
(* Proof. *)
(*   induction f. *)
(*   - easy. *)
(*   - split; simpl; intro; destruct H. *)
(*     + left. apply covering_forall_constraint. exact H. *)
(*     + right. apply IHf. exact H. *)
(*     + left. apply covering_forall_constraint. exact H. *)
(*     + right. apply IHf. exact H. *)
(* Defined. *)
      
Theorem constraint_dec {n : nat} (c : constraint n) : {empty_constraint c} + {~ empty_constraint c}.
  revert c. induction n.
  - intro c. left. intros [m p]. inversion p.
  - intro c. pose (c (last_finset n)) as l. remember l as l'. destruct l'.
    + right. intro H. specialize (H (last_finset n)). change l with (c (last_finset n)) in Heql'.
      rewrite H in Heql'. inversion Heql'.
    + specialize (IHn (c o (finset_inj n))). destruct IHn.
      * left. intros [m p]. destruct (Compare_dec.le_lt_eq_dec (S m) (S n) p) as [H1 | H1].
        -- apply le_S_n in H1. specialize (e (exist (fun m : nat => m < n) m H1)).
           compute in e. rewrite <- e. erewrite (Peano_dec.le_unique _ _ p (le_S (S m) n H1)). reflexivity.
        -- inversion H1. destruct H0. rewrite Heql'. unfold l. compute.
           erewrite (Peano_dec.le_unique _ _ p (PeanoNat.Nat.lt_succ_diag_r m)). reflexivity.
      * right. intro H1. apply n0. intro m. specialize (H1 (finset_inj n m)). rewrite <- H1. reflexivity.
Qed.



Theorem covering_dec {n : nat} (f : face_lattice n) : {covering f} + {~ covering f}.
  induction f.
  - right. intro H. inversion H.
  - destruct IHf.
    + left. simpl. now right.
    + destruct (constraint_dec a).
      * left. simpl. now left.
      * right. intros [H1 | H1] ; easy.
Qed.


(* Definition reduce_constraint_forall {p : nat} : (constraint (S p) -> constraint p). *)
(*   intro f. *)
(*   destruct f. *)
(*   - apply Some; destruct admitok. *)
(*   - exact None. *)
(* Defined. *)


(* Fixpoint  cube_to_vector {p : nat} : cube p -> Vector.t bool p. *)
(*   destruct p. *)
(*   - intro c. apply Vector.nil. *)
(*   - intro c. apply Vector.cons. *)
(*     + exact (c (last_finset p)). *)
(*     + apply (cube_to_vector p).  *)
(*       exact (c o (finset_inj p)). *)
(* Defined. *)

(* Fixpoint vector_to_cube {p : nat} (v : Vector.t bool p) : cube p. *)
(*   destruct v. *)
(*   - intro k. destruct k. easy. *)
(*   - specialize (vector_to_cube n v). *)
(*     intros [k Hk]. *)
(*     destruct (Compare_dec.lt_eq_lt_dec k n) as [[H|H]|H]. *)
(*     + exact (vector_to_cube (exist _ k H)). *)
(*     + exact h. *)
(*     + easy. *)
(* Defined. *)

(* Lemma cube_to_cube {p : nat} : forall c : cube p, vector_to_cube (cube_to_vector c) = c. *)
(* Proof. *)
(*   induction p. *)
(*   - intros. apply funext. intros [x Hx]. easy. *)
(*   - intros. apply funext. intros [k Hk]. simpl. *)
(*     destruct (Compare_dec.lt_eq_lt_dec k p) as [[H|H]|H]. *)
(*     + simpl. rewrite IHp. unfold finset_inj. unfold fcompose. repeat f_equal. *)
(*       apply Peano_dec.le_unique. *)
(*     + unfold last_finset. destruct H. repeat f_equal. apply Peano_dec.le_unique. *)
(*     + easy. *)
(* Defined. *)

(* Lemma vector_to_vector {p : nat} : forall v : Vector.t bool p, cube_to_vector (vector_to_cube v) = v. *)
(* Proof. *)
(*   intro v. *)
(*   induction v. *)
(*   - simpl. reflexivity. *)
(*   - simpl. destruct (Compare_dec.lt_eq_lt_dec n n)as [[H|H]|H]; try easy. clear H. *)
(*     apply f_equal. *)
(*     unfold fcompose.  *)
(*     match goal with *)
(*     | |- cube_to_vector ?c = _ => assert (c = vector_to_cube v) *)
(*     end. *)
(*     { apply funext. *)
(*       intros [k Hk]. *)
(*       simpl. destruct (Compare_dec.lt_eq_lt_dec k n) as [[H|H]|H]. *)
(*       + repeat f_equal. apply Peano_dec.le_unique. *)
(*       + easy. *)
(*       + easy. *)
(*     } *)
(*     rewrite H. exact IHv. *)
(* Defined. *)

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

(* Fixpoint empty_forall_in_list_dec {p : nat} ( f : 1 ~> p -> constraint p) (l : list (Vector.t bool (Nat.pow 2 p))) : *)
(*   {forall x : 1 ~> p, appears_in (arrow_to_vector x) l -> empty_constraint (f x)} + *)
(*   {(exists x : 1 ~> p, appears_in (arrow_to_vector x) l /\ ~ empty_constraint (f x))}. *)
(* Proof. *)
(*   destruct l. *)
(*   - left. *)
(*     intros x H. *)
(*     inversion H. *)
(*   - destruct (constraint_dec (f (vector_to_arrow t))) as [Ha|Ha]. *)
(*     + destruct (empty_forall_in_list_dec p f l) as [IHl|IHl]. *)
(*       * left. intro x. *)
(*         intro H. destruct (vector_bool_dec  (arrow_to_vector x) t). subst t. rewrite arrow_to_arrow in Ha. exact Ha. *)
(*         remember (t :: l) as l'. destruct H. inversion Heql'. easy. inversion Heql'. clear Heql'. subst l0. subst y. *)
(*         exact (IHl x H). *)
(*       * right. destruct IHl. *)
(*         exists x. destruct H. split. *)
(*         -- constructor. assumption. *)
(*         -- assumption. *)
(*     + right. exists (vector_to_arrow t). *)
(*       split. *)
(*       * rewrite vector_to_vector. constructor. *)
(*       * assumption. *)
(* Defined. *)

Fixpoint empty_forall_covering_in_list_dec {p : nat} ( f : 1 ~> p -> face_lattice p) (l : list (Vector.t bool (Nat.pow 2 p))) :
  {forall x : 1 ~> p, appears_in (arrow_to_vector x) l -> covering (f x)} +
  {Σ x : 1 ~> p, appears_in (arrow_to_vector x) l /\ ~ covering (f x)}.
Proof.
  destruct l.
  - left.
    intros x H.
    inversion H.
  - destruct (covering_dec (f (vector_to_arrow t))) as [Ha|Ha].
    + destruct (empty_forall_covering_in_list_dec p f l) as [IHl|IHl].
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
  

Definition forall_covering_dec {p : nat} (f : 1 ~> p ->  face_lattice p)  :
  {forall i : 1 ~> p, covering (f i)} +  {Σ i : 1 ~> p, ~ covering (f i)}.
Proof.
  destruct (empty_forall_covering_in_list_dec f (list_all (Nat.pow 2 p))).
  - left. intro i. apply c. apply all_vector_appear.
  - right. destruct s. destruct a. exists x. exact H0.
Defined.



(* Definition forall_constraint {p : nat} (f : 1 ~> p ->  constraint p): option (constraint p). *)
(*   destruct (forall_covering_dec f). *)
(*   - exact (fun _ => None). *)
(*   - exact (None). *)
(*   - exact None. *)
(*   (* -  destruct e. *) *)
(*   (* destruct (forall_covering'_dec f). *) *)
(*   (* destruct p. *) *)
(*   (* - simpl in f. *) *)
(*   (*   remember (constraint_dec (f (fun _ _ => true))) as ftrue. *) *)
(*   (*   remember (constraint_dec (f (fun _ _ => false))) as ffalse. *) *)
(*   (*   destruct ftrue, ffalse. *) *)
(*   (*   + exact (Some (fun _ => None)). *) *)
(*   (*   + exact None. *) *)
(*   (*   + exact None. *) *)
(*   (*   + exact None. *) *)
(*   (* - unfold arrow in *.  *) *)
(*   (*   remember (fun X => reduce_constraint_forall (f (X o degen_c (last_finset p)))). *) *)
(*   (*   specialize (forall_constraint p c). *) *)
(*   (*   destruct forall_constraint as [Hc|]. *) *)
(*   (*   + apply Some. intros [k Hk]. *) *)
(*   (*     destruct (Compare_dec.lt_eq_lt_dec k p) as [[H|H]|H]. *) *)
(*   (*     * apply Hc. exists k. exact H. *) *)
(*   (*     * exact None. *) *)
(*   (*     * easy. *) *)
(*   (*   + exact None. *) *)
(* Defined. *)

        
(* Lemma forall_covering {n : nat} (f : 1 ~> n ->  constraint n) : *)
(*   empty_constraint (forall_constraint f) <-> forall i : 1 ~> n, empty_constraint (f i). *)
(* Proof. *)
(*   split; intro H. *)
(*   - intro i. unfold forall_constraint in H. *)
(*     destruct (f_is_none_dec f). *)
(*     + destruct (forall_covering'_dec (f_is_none_dec' f e)). *)
(*       * unfold empty_constraint. rewrite (f_is_none_dec'_correct f e). exact (e0 i). *)
(*       *  inversion H. *)
(*     + inversion H. *)
(*   - unfold forall_constraint. *)
(*     destruct (f_is_none_dec f). *)
(*     + destruct (forall_covering'_dec (f_is_none_dec' f e)). *)
(*       * simpl. unfold empty_constraint'. intro i.  reflexivity. *)
(*       * simpl. *)
(*         apply n0. intro i. specialize (H i). rewrite (f_is_none_dec'_correct f e) in H. simpl in H. exact H. *)
(*     + destruct e. specialize (H x). *)
(*       rewrite H0 in H. exact H. *)
(* Defined. *)

                                                       
Definition forall_faces {n : nat} (f : 1 ~> n -> face_lattice n) : face_lattice n.
  destruct (forall_covering_dec f).
  - exact ([fun _ => None]).
  - exact [].
Defined.
  

Theorem forall_faces_covering {n : nat} (f : 1 ~> n -> face_lattice n) : covering (forall_faces f) <-> forall i : 1 ~> n, covering (f i).
  split.
  - intros H i.
    unfold forall_faces in H. destruct (forall_covering_dec f).
    + exact (c i).
    + inversion H.
  - intro H. unfold forall_faces.  destruct (forall_covering_dec f).
    + simpl. left. intro k. reflexivity.
    + destruct s. specialize (H x). exact (n0 H).
Defined.

    
    

(* Should I setoid ? Should I SProp *)

Inductive F : Type :=
|F1 : I -> F
|F0 : I -> F
|For : F -> F -> F
|Fand : F -> F -> F
|Fforall : (I -> F) -> F.







(* Run TemplateProgram (tImplementTC ax4_TC "F_TC" "F" Type). *)
(* Next Obligation. *)
(*   exact (face_lattice p0). *)
(* Defined. *)



(* (* Definition box_constraint {p q : nat} (α : p ~> q) (c2 : constraint q) : constraint p. *) *)
(* (* unfold constraint in *; unfold arrow in *; unfold cube in *. *) *)

(* (* Definition restrict {p q : nat} (c1 : constraint p) (α : p ~> q) (c2 : constraint q) : Prop :=  *) *)
(* (*   unfold constraint in *. unfold arrow in α. *) *)
(* (* exact (forall k : finset q, c1 a k = None -> c2 k = None) *) *)

(* Lemma empty_constraint_witness {n : nat} (c : constraint n) : {empty_constraint c} + {exists b k, c k = Some b}. *)
(* Proof. *)
(*   revert c. induction n. *)
(*   -  intro c. left. intros [m p]. inversion p. *)
(*   - intro c. pose (c (last_finset n)) as l. remember l as l'. destruct l'. *)
(*     + right. exists b. exists (last_finset n). easy. *)
(*     + specialize (IHn (c o (finset_inj n))). destruct IHn. *)
(*       * left. intros [m p]. destruct (Compare_dec.le_lt_eq_dec (S m) (S n) p) as [H1 | H1]. *)
(*         -- apply le_S_n in H1. specialize (e (exist (fun m : nat => m < n) m H1)). *)
(*            compute in e. rewrite <- e. erewrite (Peano_dec.le_unique _ _ p (le_S (S m) n H1)). reflexivity. *)
(*         -- inversion H1. destruct H0. rewrite Heql'. unfold l. compute. *)
(*            erewrite (Peano_dec.le_unique _ _ p (PeanoNat.Nat.lt_succ_diag_r m)). reflexivity. *)
(*       * right. destruct e. destruct H. exists x. exists (finset_inj n x0). exact H. *)
(* Defined. *)


(* Definition inside {p : nat} (f : constraint p) (x : cube p) := forall k : finset p, f k = None \/ f k = Some (x k). *)



(* Fixpoint inside_dec  {p : nat} (f : constraint p) (x : cube p) {struct p}: {inside f x} + {Σ k : finset p, f k = Some (negb (x k))}. *)
(* Proof. *)
(*   destruct p. *)
(*   - left. *)
(*     intros [k Hk]; easy. *)
(*   - specialize (inside_dec p (f o (finset_inj p)) (x o finset_inj p)). destruct inside_dec. *)
(*     + remember (f (last_finset p)) as fp. remember  (x (last_finset p)) as xp. *)
(*       destruct fp as [[|]|]. *)
(*       * destruct xp. *)
(*         -- left. intros [k Hk]. destruct (Compare_dec.lt_eq_lt_dec k p) as [[H | H]| H]. *)
(*            ++ specialize (i (exist _ k H)). unfold fcompose in i. simpl in i. *)
(*               assert ((le_S (S k) p H) = Hk). apply Peano_dec.le_unique. destruct H0. exact i. *)
(*            ++ destruct H. right. unfold last_finset in *. assert ((PeanoNat.Nat.lt_succ_diag_r k) = Hk). apply Peano_dec.le_unique. destruct H. rewrite <- Heqfp. rewrite <- Heqxp. reflexivity. *)
(*            ++ easy. *)
(*         -- right. exists (last_finset p). destruct Heqfp. destruct Heqxp. reflexivity. *)
(*       * destruct xp. *)
(*         -- right. exists (last_finset p). destruct Heqfp. destruct Heqxp. reflexivity. *)
(*         -- left. intros [k Hk]. destruct (Compare_dec.lt_eq_lt_dec k p) as [[H | H]| H]. *)
(*            ++ specialize (i (exist _ k H)). unfold fcompose in i. simpl in i. *)
(*               assert ((le_S (S k) p H) = Hk). apply Peano_dec.le_unique. destruct H0. exact i. *)
(*            ++ destruct H. right. unfold last_finset in *. assert ((PeanoNat.Nat.lt_succ_diag_r k) = Hk). apply Peano_dec.le_unique. destruct H. rewrite <- Heqfp. rewrite <- Heqxp. reflexivity. *)
(*            ++ easy. *)
(*       * left. intros [k Hk]. destruct (Compare_dec.lt_eq_lt_dec k p) as [[H | H]| H]. *)
(*         ++ specialize (i (exist _ k H)). unfold fcompose in i. simpl in i. *)
(*            assert ((le_S (S k) p H) = Hk). apply Peano_dec.le_unique. destruct H0. exact i. *)
(*         ++ destruct H. left. unfold last_finset in Heqfp. *)
(*            assert ((PeanoNat.Nat.lt_succ_diag_r k) = Hk). apply Peano_dec.le_unique. destruct H. easy. *)
(*         ++ easy. *)
(*     + right. destruct s as [[k Hk] H]. unfold fcompose in H. simpl in H. *)
(*       exists (exist (fun m : nat => m < S p) k (le_S (S k) p Hk)). easy. *)
(* Defined. *)


(* Lemma witness_not_inside {p : nat} (f : constraint p) : (exists b k, f k = Some b) <-> (exists x : cube p, ~ (inside f x)). *)
(* Proof. *)
(*   split.  *)
(*   - intro H. destruct H as [b H]. destruct H as [[x Hx] H]. *)
(*     unshelve refine (ex_intro _ _ _). *)
(*     +  intros [k Hk]. *)
(*        destruct  (Compare_dec.lt_eq_lt_dec k x) as [[H1 | H1] | H1]. *)
(*        * exact true. *)
(*        * exact (negb b). *)
(*        * exact true. *)
(*     + intro H1. *)
(*       unfold inside in H1. specialize (H1 (exist (fun m : nat => m < p) x Hx)). *)
(*       rewrite H in H1. destruct H1. *)
(*       * easy. *)
(*       * destruct (Compare_dec.lt_eq_lt_dec x x) as [[H1 | H1] | H1]; destruct b; easy. *)
(*   - intro. destruct H. destruct (inside_dec f x). *)
(*     + easy. *)
(*     + destruct s. exists (negb (x x0)). exists x0. assumption. *)
(* Defined. *)


(* Lemma empty_inside {p : nat} (f : constraint p) : empty_constraint f <-> forall x : cube p, inside f x. *)
(* Proof.  *)
(*   split; intro H. *)
(*   - intros x.  *)
(*     destruct (inside_dec f x). *)
(*     + exact i. *)
(*     + destruct s. unfold empty_constraint in H. specialize (H x0). rewrite H in e. easy. *)
(*   - destruct (empty_constraint_witness f). *)
(*     + exact e. *)
(*     + apply witness_not_inside in e. destruct e. specialize (H x). easy. *)
(* Defined. *)

(* Definition restricts_constraint_aux {p q : nat} (f1 : constraint p) (α : p ~> q) (f2 : constraint q) := *)
(*   forall x : cube q, (inside f1 (α x) -> inside f2 x). *)

(* Lemma restricts_constraint_aux_covering {p q : nat} (f1 : constraint p) (α : p ~> q) (f2 : constraint q) : *)
(*   restricts_constraint_aux f1 α f2 -> empty_constraint f1 -> empty_constraint f2. *)
(* Proof. *)
(*   intros.  unfold restricts_constraint_aux in *. *)
(*   destruct (empty_constraint_witness f2). *)
(*   - exact e. *)
(*   - apply witness_not_inside  in e. *)
(*     destruct e. *)
(*     specialize (H x). rewrite empty_inside in H0. specialize (H0 (α x)). *)
(*     apply H in H0. easy. *)
(* Defined. *)


(* Lemma restricts_constraint_aux_meet {p q : nat} (f : constraint p) (α : p ~> q) (a b : constraint q) : *)
(*   restricts_constraint_aux f α a /\ restricts_constraint_aux f α b -> restricts_constraint_aux f α (meet_constraint a b). *)
(* Proof. *)
(*   intros. destruct H. unfold restricts_constraint_aux. *)
(*   intro x. *)
(*   intro H1. *)
(*   unfold restricts_constraint_aux in H, H0. *)
(*   specialize (H x).  specialize (H0 x). specialize (H H1). specialize (H0 H1). *)
(*   unfold inside. unfold meet_constraint. destruct (meetable_dec a b). *)
(*   - intro k. specialize (H k). specialize (H0 k). *)
(*     destruct H, H0; rewrite H; try rewrite H0; destruct (x k); auto. *)
(*   - unfold inside in *. destruct e as [k [b0 [Ha Hb]]]. *)
(*     specialize (H k). specialize (H0 k). rewrite Ha in H. rewrite Hb in H0. clear Ha Hb. *)
(*     destruct H, H0. *)
(*     * inversion H. *)
(*     * inversion H. *)
(*     * inversion H0. *)
(*     * inversion H. destruct H3. destruct b0; easy. *)
(* Defined. *)


(* Lemma restrict_constraint_rev {p q : nat} (f : constraint p) (α : p ~> q) (a b : constraint q) : *)
(*    restricts_constraint_aux f α (meet_constraint a b) -> restricts_constraint_aux f α a. *)
(* Proof. *)
(*   intros. *)
(*   unfold restricts_constraint_aux in *. intro x. intro Hf. specialize (H x Hf). *)
(*   intro k. specialize (H k). destruct H. *)
(*   - unfold meet_constraint in H. destruct (a k). inversion H. left. reflexivity. *)
(*   - unfold meet_constraint in H. destruct (a k). right. exact H. left. reflexivity. *)
(* Defined. *)

(* Lemma restricts_constraint_aux_meet' {p q : nat} (f f' : constraint p) (α : p ~> q) (a : constraint q) (Hmeet : meetable f f'): *)
(*   restricts_constraint_aux f α a \/ restricts_constraint_aux f' α a -> restricts_constraint_aux (meet_constraint f f') α a. *)
(* Proof. *)
(*   intros. unfold restricts_constraint_aux in *. intros x Hx.  *)
(*   destruct H; specialize (H x); apply H. *)
(*   - intro k. specialize (Hx k).  unfold meet_constraint in Hx. *)
(*     destruct (f k); destruct (Hx); easy. *)
(*   -  intro k. specialize (Hx k). unfold meet_constraint in Hx. *)
(*         remember (f k) as fk. remember (f' k) as f'k. destruct (fk) as [[|]|]; destruct (f'k) as [[|]|]; destruct Hx; auto. *)
(*         -- inversion H0. *)
(*         -- unfold meetable in Hmeet. specialize (Hmeet k true false). *)
(*            destruct Heqfk, Heqf'k. specialize (Hmeet (conj eq_refl eq_refl)). inversion Hmeet. *)
(*         -- inversion H0. *)
(*         -- unfold meetable in Hmeet. specialize (Hmeet k false true). *)
(*            destruct Heqfk, Heqf'k. specialize (Hmeet (conj eq_refl eq_refl)). inversion Hmeet. *)
(* Defined. *)

(* Fixpoint restricts_constraint {p q : nat} (f1 : constraint p) (α : p ~> q) (f2 : face_lattice q) := *)
(*   match f2 with *)
(*   | []  => forall x : cube q, exists k, f1 k = Some (negb (α x k)) *)
(*   | c :: f'2 => restricts_constraint_aux f1 α c \/ restricts_constraint f1 α f'2 *)
(*   end. *)


(* Lemma restricts_constraint_meet' {p q : nat} (f f' : constraint p) (α : p ~> q) (a : face_lattice q) (Hmeet : meetable f f'): *)
(*   restricts_constraint f α a \/ restricts_constraint f' α a -> restricts_constraint (meet_constraint f f') α a. *)
(* Proof. *)
(*   induction a. *)
(*   - simpl. *)
(*     intros. destruct H. *)
(*     + specialize (H x). *)
(*       destruct H. exists x0. unfold meet_constraint. rewrite H. reflexivity. *)
(*     + specialize (H x). *)
(*       destruct H. exists x0. unfold meet_constraint. *)
(*       remember (f x0) as fx0. destruct fx0. *)
(*       * unfold meetable in Hmeet. specialize (Hmeet x0). f_equal. apply Hmeet. symmetry in Heqfx0. exact (conj Heqfx0 H). *)
(*       * assumption. *)
(*   - simpl; intro H. destruct H as [[H | H] | [H | H]]. *)
(*     + left. apply restricts_constraint_aux_meet'. exact Hmeet. left. exact H. *)
(*     + right. apply IHa. left. exact H. *)
(*     + left. apply restricts_constraint_aux_meet'. exact Hmeet. right. exact H. *)
(*     + right. apply IHa. right. exact H. *)
(* Defined. *)

(* Lemma restricts_constraint_covering {p q : nat} (f1 : constraint p) (α : p ~> q) (f2 : face_lattice q) : *)
(*   restricts_constraint f1 α f2 -> empty_constraint f1 -> covering f2. *)
(* Proof. *)
(*   intros. induction f2. *)
(*   - unfold empty_constraint in H0. unfold restricts_constraint in H. *)
(*     simpl. specialize (H (fun _ => true)). destruct H. specialize (H0 x). rewrite H in H0. inversion H0. *)
(*   - simpl in H. simpl. destruct H. *)
(*     + left. exact (restricts_constraint_aux_covering f1 α a H H0). *)
(*     + right. exact (IHf2 H). *)
(* Defined. *)

(* Fixpoint restricts {p q : nat} (f1 : face_lattice p) (α : p ~> q) (f2 : face_lattice q):= *)
(*   match f1 with *)
(*   | [] => True *)
(*   | c :: f'1 => restricts_constraint c α f2 /\ restricts f'1 α f2 *)
(*   end. *)


                         
(* Theorem restrict_covering {p q : nat} {α : p ~> q} {f1 : face_lattice p} {f2 : face_lattice q} *)
(*         (H : restricts f1 α f2) *)
(*   : covering f1 -> covering f2. *)
(* Proof. *)
(*   intros. induction f1. *)
(*   - easy. *)
(*   - simpl in H. simpl in H0. destruct H. destruct H0. *)
(*     + exact (restricts_constraint_covering a α f2 H H0). *)
(*     + exact (IHf1 H1 H0). *)
(* Defined. *)


(* Fixpoint f_alpha_empty_dec {p q : nat} (f : constraint p) (α : p ~> q) {struct q}: *)
(*   {forall x, Σ k, f k = Some (negb (α x k))} + {Σ x,  inside f (α x)}. *)
(*   destruct q.  *)
(*   - destruct (inside_dec f (α (fun _ => true))). *)
(*     + right. exists (fun _ => true). exact i. *)
(*     + left. intro x. destruct s. exists x0. rewrite e. repeat f_equal. apply funext. intros [y Hy]. easy. *)
(*   - destruct (f_alpha_empty_dec p q f (α o face_c (last_finset q) true)). *)
(*     + destruct (f_alpha_empty_dec p q f (α o face_c (last_finset q) false)). *)
(*       * left. intro x. remember (x (last_finset q)) as xq. destruct xq. *)
(*         -- specialize (s (degen_c (last_finset q) x)). *)
(*            destruct s as [k Hfk]. *)
(*            exists k. rewrite Hfk. repeat f_equal. *)
(*            unfold fcompose. f_equal. apply funext. *)
(*            intros [h Hh]. simpl. destruct (lt_eq_lt_dec h q) as [[H | H] | H]. *)
(*            ++ repeat f_equal. apply Peano_dec.le_unique. *)
(*            ++ subst h. rewrite Heqxq. unfold last_finset. repeat f_equal. apply Peano_dec.le_unique. *)
(*            ++ easy. *)
(*         -- specialize (s0 (degen_c (last_finset q) x)). *)
(*            destruct s0 as [k Hfk]. *)
(*            exists k. rewrite Hfk. repeat f_equal. *)
(*            unfold fcompose. f_equal. apply funext. *)
(*            intros [h Hh]. simpl. destruct (lt_eq_lt_dec h q) as [[H | H] | H]. *)
(*            ++ repeat f_equal. apply Peano_dec.le_unique. *)
(*            ++ subst h. rewrite Heqxq. unfold last_finset. repeat f_equal. apply Peano_dec.le_unique. *)
(*            ++ easy. *)
(*       * right. destruct s0. *)
(*         unshelve refine (existT _ _). *)
(*         -- intros [k Hk]. *)
(*            destruct (lt_eq_lt_dec k q) as [[H|H]|H]. *)
(*            ++ exact (x (exist _ k H)). *)
(*            ++ exact false. *)
(*            ++ easy. *)
(*         -- intro k. *)
(*            specialize (i k). *)
(*            destruct i. *)
(*            ++ left. assumption. *)
(*            ++ right. rewrite H. unfold fcompose, face_c, last_finset. destruct k as [k Hk]. repeat f_equal. *)
(*               apply funext. intros [h Hh]. destruct (lt_eq_lt_dec h q) as [[H'|H']|H']. *)
(*               ** repeat f_equal. apply Peano_dec.le_unique. *)
(*               ** reflexivity. *)
(*               ** easy. *)
(*     + right. destruct s. *)
(*       unshelve refine (existT _ _). *)
(*       * intros [k Hk]. *)
(*         destruct (lt_eq_lt_dec k q) as [[H|H]|H]. *)
(*         -- exact (x (exist _ k H)). *)
(*         -- exact true. *)
(*         -- easy. *)
(*       * intro k. *)
(*         specialize (i k). *)
(*         destruct i. *)
(*         -- left. assumption. *)
(*         -- right. rewrite H. unfold fcompose, face_c, last_finset. destruct k as [k Hk]. repeat f_equal. *)
(*            apply funext. intros [h Hh]. destruct (lt_eq_lt_dec h q) as [[H'|H']|H']. *)
(*            ++ repeat f_equal. apply Peano_dec.le_unique. *)
(*            ++ reflexivity. *)
(*            ++ easy. *)
(* Defined. *)

(* Definition f_nonempty_or_restricts_all_dec {p q : nat} (f : constraint p) (α : p ~> q): *)
(*   {forall g : constraint q, restricts_constraint_aux f α g} + {Σ x, inside f (α x)}. *)
(*   destruct (f_alpha_empty_dec f α). *)
(*   - left. *)
(*     intros g x H. *)
(*     specialize (s x). *)
(*     destruct s as [k Hk]. specialize (H k). *)
(*     rewrite Hk in H; destruct H; inversion H. *)
(*     destruct (α x k); inversion H. *)
(*   - right. assumption. *)
(* Defined. *)


(* Definition f_nonempty_or_restricts_all_dec_aux {p q : nat} (f : constraint p) (α : p ~> q): *)
(*   {forall g : face_lattice q, restricts_constraint f α g} + {Σ x, inside f (α x)}. *)
(*   destruct (f_alpha_empty_dec f α). *)
(*   - left. *)
(*     induction g. *)
(*     + simpl. *)
(*       intro x. specialize (s x). destruct s. exists x0. exact e. *)
(*     + simpl. right. exact IHg. *)
(*   - right. assumption. *)
(* Defined. *)


(* Lemma restricts_constraint_join {p q : nat} (f : constraint p) (α : p ~> q) (g1 g2 : face_lattice q) : *)
(*   restricts_constraint f α g1 \/ restricts_constraint f α g2 -> restricts_constraint f α (join_faces g1 g2). *)
(* Proof. *)
(*   induction g1. *)
(*   - simpl. intro. *)
(*     destruct H. *)
(*     + destruct (f_nonempty_or_restricts_all_dec_aux f α). *)
(*       * apply r. *)
(*       * destruct s. specialize (H x). destruct H. specialize (i x0). *)
(*         rewrite H in i; destruct i as [i | i]; destruct (α x x0); inversion i. *)
(*     + exact H. *)
(*   - simpl. intro. destruct H as [[H | H] | H]. *)
(*     + left. exact H. *)
(*     + right. apply IHg1. left. exact H. *)
(*     + right. apply IHg1. right. exact H. *)
(* Defined. *)



(* Lemma restricts_constraint_meet_aux {p q : nat} (f : constraint p) (α : p ~> q) (a : constraint q) (g : face_lattice q) : *)
(*   restricts_constraint_aux f α a /\ restricts_constraint f α g -> restricts_constraint f α (meet_faces_aux a g). *)
(* Proof. *)
(*   induction g. *)
(*   - intros. destruct H. exact H0. *)
(*   - intros. simpl. destruct (meetable_dec a a0). *)
(*     + destruct H. destruct H0; simpl in *.  *)
(*       * left. apply restricts_constraint_aux_meet. exact (conj H H0). *)
(*       * right. apply IHg. exact (conj H H0). *)
(*     + simpl in H. destruct H as [Hfa [Hfa0 | Hfg]]. *)
(*       -- assert (H := restricts_constraint_aux_meet f α a a0 (conj Hfa Hfa0)). *)
(*          destruct (f_nonempty_or_restricts_all_dec_aux f α). *)
(*          ++ apply r. *)
(*          ++ destruct s. destruct e as [k [b [Ha Ha0]]]. *)
(*             specialize (Hfa x i). *)
(*             specialize (Hfa0 x i). *)
(*             unfold inside in *. specialize (Hfa k). specialize (Hfa0 k). *)
(*             destruct Hfa, Hfa0; rewrite H0 in Ha; rewrite H1 in Ha0; inversion Ha; inversion Ha0. *)
(*             rewrite H3 in H4. destruct b;  inversion H4. *)
(*       -- apply IHg. exact (conj Hfa Hfg). *)
(* Defined. *)



(* Lemma restricts_constraint_meet'_aux {p q : nat} (f : face_lattice p)  (a : constraint p) (α : p ~> q) (g : face_lattice q) : *)
(*    restricts_constraint a α g \/ restricts f α g -> restricts (meet_faces_aux a f) α g. *)
(* Proof. *)
(*   induction f. *)
(*   - intros. simpl. easy. *)
(*   - intros. simpl. *)
(*     + destruct (meetable_dec a a0). *)
(*       * destruct H; split. *)
(*         -- apply restricts_constraint_meet'. exact m.  left. apply H. *)
(*         -- apply IHf. left. exact H. *)
(*         -- apply restricts_constraint_meet'.  simpl in H. destruct H. apply m. right. simpl in H.  destruct H. exact H. *)
(*         -- simpl in H. apply IHf. destruct H. right. exact H0. *)
(*       * apply IHf. *)
(*         destruct H. *)
(*         -- left. apply H. *)
(*         -- simpl in H. right. destruct H. exact H0. *)
(* Defined. *)
      
(* Lemma restricts_constraint_meet {p q : nat} (f : constraint p) (α : p ~> q) (g1 g2 : face_lattice q) : *)
(*   restricts_constraint f α g1 /\ restricts_constraint f α g2 -> restricts_constraint f α (meet_faces g1 g2). *)
(* Proof. *)
(*   induction g1. *)
(*   - simpl. intro. *)
(*     destruct H. *)
(*     easy. *)
(*   - simpl. intro. destruct H as [[H | H]  H1]. *)
(*     + apply restricts_constraint_join. left. *)
(*       apply restricts_constraint_meet_aux. exact (conj H H1). *)
(*     + apply restricts_constraint_join. right. *)
(*       exact (IHg1 (conj H H1)). *)
(* Defined. *)

(* Lemma test {p q : nat} (f : constraint p) (α : p ~> q) (g : face_lattice q) : *)
(*   (covering g) -> restricts_constraint f α g. *)
(* Proof. *)
(*   induction g. *)
(*   - intro. inversion H. *)
(*   - simpl; intro. destruct H. *)
(*     + left. *)
(*       intros x Hf k. specialize (H k). left. assumption. *)
(*     + right. apply IHg. assumption. *)
(* Defined. *)

(* Lemma restrict_covering_forall_left {p q : nat} (f : (1 ~> p) -> face_lattice p) (α : p ~> q) (g : face_lattice q) : *)
(*   (exists i : (1 ~> p), restricts (f i) α g) -> restricts (forall_faces f) α g. *)
(* Proof. *)
(*   intro. *)
(*   unfold forall_faces. destruct (forall_covering_dec f). *)
(*   - simpl. split; try constructor. *)
(*     destruct H. specialize (c x). apply restrict_covering in H. *)
(*     apply test. exact H. apply c. *)
(*   - simpl. easy. *)
(* Defined. *)

(* Lemma restrict_covering_forall_right {p q : nat} (f : constraint p) (α : p ~> q) (g : (1 ~> q) ->  face_lattice q) : *)
(*   (forall i : (1 ~> q), restricts_constraint f α (g i)) -> restricts_constraint f α (forall_faces g). *)
(* Proof. *)
(*   intro H. *)
(*   unfold forall_faces. destruct (forall_covering_dec g). *)
(*   -  apply test. simpl. left. intro k. reflexivity. *)
(*   - destruct s. specialize (H x). *)

(*     assert (exists i : 1 ~> q, covering (g i)). *)
(*     induction g. *)
(*     + simpl. destruct H.  *)
(*     unfold restricts_constraint. *)
  
  
(* Lemma restrict_covering_forall_false {p q : nat} (f : (1 ~> p) -> face_lattice p) (α : p ~> q) (g : (1 ~> q) -> face_lattice q) : *)
(*   (forall i : (1 ~> p), restricts (f i) α (g (α ô i))) -> restricts (forall_faces f) α (forall_faces g). *)
(* Proof. *)
(*   intro. *)
(*   unfold forall_faces. destruct (forall_covering_dec f). *)
(*   - destruct (forall_covering_dec g). *)
(*     + simpl. split. *)
(*       * unfold restricts_constraint_aux. left. *)
(*         intros x Hf k. left. reflexivity. *)
(*       * easy. *)
(*     + SearchAbout restricts. *)
(*       unfold restricts in H. *)
  
(* (* Abort. *) *)

(* (* Lemma restrict_covering_None  *) *)
  
(* (* Lemma restrict_covering_forall_false {p : nat} (f : (1 ~> p) -> constraint p) (g : forall q : nat, (p ~> q) -> (1 ~> q) -> constraint q) : *) *)
(* (*   (forall i : (1 ~> p), forall q α, restricts_constraint_aux (f i) α (g q α (α ô i))) -> *) *)
(* (*   forall q α, restricts_constraint_aux (forall_constraint f) α (forall_constraint (g q α)). *) *)
(* (* Proof. *) *)
(* (*   intro H. *) *)
(* (*   intros q α. *) *)
(* (*   unfold restricts_constraint_aux in *. intro x. *) *)
(* (*   intro Hx. unfold inside. *) *)
(* (*   unfold forall_constraint in *. *) *)
(* (*   - destruct (f_is_none_dec f). *) *)
(* (*     +  *) *)
  
  
(*   (*   intro H. *) *)
(* (*   unfold restricts_constraint_aux. intro x. *) *)
(* (*   unfold restricts_constraint_aux in H. *) *)
(* (*   intro Hfx. *) *)
(* (*   unfold forall_constraint. *) *)
(* (*   destruct (f_is_none_dec g). *) *)
(* (*   - destruct (forall_covering'_dec (f_is_none_dec' g e)); unfold inside. *) *)
(* (*     + intro k. left. reflexivity. *) *)
(* (*     + apply n. clear n. intro i. *) *)
(* (*       destruct (empty_constraint'_witness (f_is_none_dec' g e i)). *) *)
(* (*       * exact e0. *) *)
(* (*       * destruct e0 as [b [k Hg]]. *) *)
        
(* (*   destruct inside'_dec *) *)
(* (*   intro Hx. unfold inside in *. *) *)
(* (*   unfold forall_constraint in *. *) *)
(* (*   destruct (f_is_none_dec g). *) *)
(* (*   - destruct (forall_covering'_dec (f_is_none_dec' g e)); *) *)
(* (*       unfold restricts_constraint_aux in H. *) *)
(* (*     + unfold inside'. intro k. left. reflexivity. *) *)
(* (*     + apply n; clear n. intro i. *) *)
(* (*       destruct (empty_constraint'_witness (f_is_none_dec' g e i)). *) *)
(* (*       * exact e0. *) *)
(* (*       * destruct e0. destruct H0. *) *)
(* (*         destruct (f_is_none_dec f). *) *)
(* (*         -- destruct (forall_covering'_dec (f_is_none_dec' f e0)). *) *)
(* (*            specialize (H (α ô i)). *) *)
      


      
(* (*   remember (forall_constraint f) as forall_f. *) *)
(* (*   destruct (forall_f). *) *)
(* (*   - unfold forall_constraint in *. *) *)
(* (*   destruct (f_is_none_dec f). *) *)
(* (*   - destruct (f_is_none_dec g). *) *)
(* (*     + simpl in Hx. *) *)
  

  

(* Lemma restrict_join {p q : nat} (f : face_lattice p) (α : p ~> q) (g1 g2: face_lattice q) : *)
(*   restricts f α g1 \/ restricts f α g2 -> restricts f α (join_faces g1 g2). *)
(* Proof. *)
(*   induction f; simpl; intros. *)
(*   - reflexivity. *)
(*   - destruct H as [[H H1] | [H H1]]; apply conj. *)
(*     + apply restricts_constraint_join. *)
(*       left. exact H. *)
(*     + apply IHf. *)
(*       left. exact H1. *)
(*     + apply restricts_constraint_join. *)
(*       right. exact H. *)
(*     + apply IHf. *)
(*       right. exact H1. *)
(* Defined. *)

(* Lemma restrict_join' {p q : nat} (f1 f2 : face_lattice p) (α : p ~> q) (g: face_lattice q) : *)
(*   restricts f1 α g /\ restricts f2 α g -> restricts (join_faces f1 f2) α g. *)
(* Proof. *)
(*   induction f1; simpl; intros. *)
(*   - destruct H; easy. *)
(*   - apply conj; destruct H as [[H H1 ] H2]. *)
(*     + exact H. *)
(*     + apply IHf1. *)
(*       * apply conj. *)
(*         -- exact H1. *)
(*         -- exact H2. *)
(* Defined. *)

(* Lemma restrict_meet {p q : nat} (f : face_lattice p) (α : p ~> q) (g1 g2: face_lattice q) : *)
(*   restricts f α g1 /\ restricts f α g2 -> restricts f α (meet_faces g1 g2). *)
(* Proof. *)
(*   induction f; simpl; intros. *)
(*   - reflexivity. *)
(*   - destruct H as [[H H1] [H2 H3]]; apply conj. *)
(*     + apply restricts_constraint_meet. exact (conj H H2). *)
(*     + apply IHf. exact (conj H1 H3). *)
(* Defined. *)


(* Lemma restrict_meet' {p q : nat} (f1 f2 : face_lattice p) (α : p ~> q) (g: face_lattice q) : *)
(*   restricts f1 α g \/ restricts f2 α g -> restricts (meet_faces f1 f2) α g. *)
(* Proof. *)
(*   induction f1; simpl; intros. *)
(*   - easy. *)
(*   - apply restrict_join'. destruct H as [[H H1] | H]; apply conj. *)
(*     + apply restricts_constraint_meet'_aux. left. exact H. *)
(*     + apply IHf1. left. exact H1. *)
(*     + apply restricts_constraint_meet'_aux. right. exact H. *)
(*     + apply IHf1. right. exact H. *)
(* Defined. *)



(* Run TemplateProgram (tImplementTC F_TC "natf_TC" "natf" (F -> Prop)). *)
(* Next Obligation. *)
(*   rename X into f. rename α into α0. *)
(*   exact (forall (p1 : nat) (α1 : p0 ~> p1), restricts (f p0 α0) α1 (f p1 (α1 ô α0))). *)
(* Defined. *)


 

(* Run TemplateProgram (tImplementTC natf_TC "covers_TC" "covers" (F -> Prop)). *)
(* Next Obligation. *)
(*   rename α into α0. rename X into f. *)
(*   exact (covering (f p0 α0)). *)
(* Defined. *)



(* Run TemplateProgram (tImplementTC covers_TC "realize_TC" "realize" (F -> Prop)). *)
(* Next Obligation. *)
(*   unfold Fᵗ, Fᵗ_obligation_1, face_lattice in X. *)
(*   rename X into f. *)
(*   specialize (f p0 α). exact (covering f). (* the problem is probably with this one, should give more constraint *) *)
(* Defined. *)


(* Definition sieve_equiv {p : nat} (S1 S2 : forall q : nat, p ~> q -> Prop) := *)
(*   forall (q : nat) (α : p ~> q), S1 q α <-> S2 q α. *)

(* Notation "S ≈ T" := (sieve_equiv S T) (at level 65, left associativity). *)

(* (** Cofibrant propositions *) *)

(* (* Run TemplateProgram (tImplementTC realize_TC "cof_TC" "cof" (Prop -> Prop)). *) *)
(* (* Next Obligation. *) *)
(* (*   rename X into S. *) *)
(* (*   specialize (S p id). *) *)
(* (*   exact (exists f : (forall p0 : nat, p ~> p0 -> Fᵗ p0 p0 id), *) *)
(* (*             (fun (p0 : nat) (α : p ~> p0) => covering (f p0 α)) ≈ S). (** Why not cof Prop -> Type? **) *) *)
(* (* Defined. *) *)

(* (* (* this one seems a better definition. However, i need to put it in the translation database, and i dont *) *)
(* (*  know how to do this without dirty hacks. Also, I need sigma-types translation. *) *) *)
(* (* Definition cof' : Prop -> Prop := fun s => exists f : F, s = realize f. *) *)



(* Transparent degen_c. *)

(* (** axioms on cof *) *)
(* Definition extend_constraint {a : nat} (c : constraint a) : constraint (S a). *)
(*   intros [i p]. destruct i. *)
(*   - exact (None). *)
(*   - apply le_S_n in p. apply c. exists i. exact p. *)
(* Defined. *)


(* Lemma covering_extended {a : nat} (c : constraint a) : *)
(*   empty_constraint (extend_constraint c) <-> empty_constraint c. *)
(* Proof. *)
(*   split; intro H.  *)
(*   - unfold empty_constraint. unfold empty_constraint in H. unfold extend_constraint in H. *)
(*     intros [m Hm]. *)
(*     specialize (H (exist _ (S m) (Lt.lt_n_S m a Hm))). simpl in H. rewrite <- H. *)
(*     repeat f_equal. apply Peano_dec.le_unique. *)
(*   - unfold extend_constraint. *)
(*     unfold empty_constraint in *. *)
(*     intros [m Hm]. destruct m. *)
(*     + reflexivity. *)
(*     + apply H. *)
(* Defined. *)

(* Lemma covering_map {a : nat} (c : face_lattice a) : covering (map extend_constraint c) <-> covering c. *)
(* Proof. *)
(*   induction c; split; intro H. *)
(*   - simpl in *. easy. *)
(*   - simpl in *. easy. *)
(*   - simpl in *. destruct H. *)
(*     + rewrite covering_extended in H. exact (or_introl H). *)
(*     + rewrite IHc in H. *)
(*       exact (or_intror H). *)
(*   - simpl in *. destruct H. *)
(*     + apply or_introl. apply covering_extended. exact H. *)
(*     + apply or_intror. apply IHc. exact H. *)
(* Defined. *)



(* Definition destruct_eq {p : nat} (f g : cube (S p) -> cube 1) : *)
(*   (f = g) <-> (forall b : bool, (f o face_c (last_finset p) b) =  (g o face_c (last_finset p) b)). *)
(*   split. *)
(*   - intro H. destruct H. reflexivity. *)
(*   - intro H. apply funext. intro d. remember (d (last_finset p)) as dp. *)
(*     specialize (H dp). *)
(*     assert ((face_c (last_finset p) dp) (degen_c (last_finset p) d) = d). *)
(*     + apply funext. intros [x Hx]. simpl. destruct (lt_eq_lt_dec x p) as [[H1 | H1] | H1]. *)
(*       * repeat f_equal. apply Peano_dec.le_unique. *)
(*       * destruct H1. symmetry in Heqdp. destruct Heqdp. unfold last_finset. repeat f_equal. apply  Peano_dec.le_unique. *)
(*       * easy. *)
(*     + destruct H0. *)
(*       match goal with *)
(*       | |- context [f (face_c (last_finset p) dp ?x)] => change (f (face_c (last_finset p) dp x)) with ((f o face_c (last_finset p) dp) x) *)
(*       end. *)
(*       rewrite H. *)
(*       reflexivity. *)
(* Defined. *)

(* Fixpoint eq_decidable_cube {p : nat} (f g : cube p -> cube 1) {struct p}: {f = g} + { exists x k,  ~ (f x k = g x k)}. *)
(*   destruct p. *)
(*   - unfold cube in *. remember (f (fun _ => true) (zero_finset 0)) as f0. *)
(*     remember (g (fun _ => true) (zero_finset 0)) as g0. *)
(*     destruct f0, g0. *)
(*     + left. apply funext. intro x. apply funext. intro y. *)
(*       assert ((fun _ => true) = x). apply funext. intros [b Hb]. easy. destruct H. *)
(*       assert (zero_finset 0 = y). destruct y. destruct x. unfold zero_finset. f_equal. apply Peano_dec.le_unique. easy. destruct H. *)
(*       destruct Heqf0. destruct Heqg0. reflexivity. *)
(*     + right. *)
(*       exists (fun _ : finset 0 => true). exists (zero_finset 0). destruct Heqf0, Heqg0. easy. *)
(*     + right. *)
(*       exists (fun _ : finset 0 => true). exists (zero_finset 0). destruct Heqf0, Heqg0. easy. *)
(*     + left. apply funext. intro x. apply funext. intro y. *)
(*       assert ((fun _ => true) = x). apply funext. intros [b Hb]. easy. destruct H. *)
(*       assert (zero_finset 0 = y). destruct y. destruct x. unfold zero_finset. f_equal. apply Peano_dec.le_unique. easy. destruct H. *)
(*       destruct Heqf0. destruct Heqg0. reflexivity. *)
(*   - remember (f o face_c (last_finset p) true) as ftrue. *)
(*     remember (f o face_c (last_finset p) false) as ffalse. *)
(*     remember (g o face_c (last_finset p) true) as gtrue. *)
(*     remember (g o face_c (last_finset p) false) as gfalse. *)
(*     assert (eqtrue := eq_decidable_cube p ftrue gtrue). *)
(*     assert (eqfalse := eq_decidable_cube p ffalse gfalse). *)
(*     destruct eqtrue. *)
(*     * destruct eqfalse. *)
(*       -- destruct e, e0. left. *)
(*          apply destruct_eq. intro b. destruct b. *)
(*          rewrite <- Heqgtrue. rewrite <- Heqftrue. reflexivity. *)
(*          rewrite <- Heqgfalse. rewrite <- Heqffalse. reflexivity. *)
(*       -- right. destruct e. destruct e0. rewrite Heqffalse, Heqgfalse in H. destruct H. *)
(*          unfold fcompose in H. exists (face_c (last_finset p) false x). *)
(*          exists x0. exact H. *)
(*     * right. destruct e. destruct H. rewrite Heqftrue, Heqgtrue in H. *)
(*       unfold fcompose in H. exists (face_c (last_finset p) true x). exists x0. exact H. *)
(* Defined. *)


(* (** Since equality between i : cube p -> cube 1 is decidable, we define  *)
(* extremity i b := if i = I_end_map p b then None else false.  *)
(* Presumably this is not a good idea? **) *)

(* Definition extremity {p : nat} (b : bool) (i : cube p -> cube 1) : face_lattice p. *)
(*   destruct (eq_decidable_cube i (I_end_map p b)). *)
(*   - apply cons. exact (fun _ => None). exact nil. *)
(*   - exact nil. *)
(* Defined. *)
  

(* Fixpoint extremity' {p : nat} (b : bool) (i : cube p -> cube 1) {struct p}: face_lattice p.   *)
(*   destruct p. *)
(*   - unfold face_lattice. destruct (i (fun _ => true) (zero_finset 0)); destruct b. *)
(*     + exact [(fun _ => None)]. *)
(*     + exact nil. *)
(*     + exact nil. *)
(*     + exact [(fun _ => None)]. *)
(*   - pose (i0true := extremity' p b (i o (face_c (last_finset p) true))). *)
(*     pose (i0false := extremity' p b (i o (face_c (last_finset p) false))). *)
(*     apply meet_faces. unfold face_lattice. *)
(*     exact (map extend_constraint i0true). *)
(*     exact (map extend_constraint i0false). *)
(* Defined. *)



(* Theorem extremity_correct {p : nat} (b : bool) (i : cube p -> cube 1) : *)
(*   covering (extremity b i) <-> I_end_map p b = i. *)
(* Proof. *)
(*   unfold extremity. destruct ( eq_decidable_cube i (I_end_map p b)); split. *)
(*   - intro H. rewrite e. reflexivity. *)
(*   - intro H. simpl. apply or_introl. unfold empty_constraint. intro x. reflexivity. *)
(*   - intro H. destruct H. *)
(*   - intro H. destruct e. destruct H0. symmetry in H. *)
(*     apply (TFUtils.ap (fun F => F x x0)) in H. easy. *)
(* Defined. *)



(* Theorem extremity_correct' {p : nat} (b : bool) (i : cube p -> cube 1) : *)
(*   covering (extremity' b i) <-> I_end_map p b = i. *)
(* Proof. *)
(*   induction p. *)
(*   split. *)
(*   - intro. apply funext. intro d. apply funext. intro x. destruct x. unfold extremity in H. simpl in H. *)
(*   destruct x. *)
(*     + assert ((fun _ => true) = d). apply funext. intro x0. destruct x0. easy. destruct H0. *)
(*       assert ((exist (fun m : nat => m < 1) 0 l) = zero_finset 0). unfold zero_finset. f_equal. apply Peano_dec.le_unique. destruct H0. *)
(*       destruct (i (fun _ : finset 0 => true) (exist (fun m : nat => m < 1) 0 l)); destruct b. *)
(*       * reflexivity. *)
(*       * easy. *)
(*       * easy. *)
(*       * reflexivity. *)
(*     + easy. *)
(*   - intro.  simpl. destruct H. destruct b. *)
(*     + unfold I_end_map. unfold covering. unfold empty_constraint. *)
(*       apply or_introl. intro x. destruct x. easy. *)
(*     + unfold I_end_map. unfold covering. unfold empty_constraint. *)
(*       apply or_introl. intro x. destruct x. easy. *)
(*   - split; intro H. *)
(*     + simpl in H.  unfold fcompose in H. apply covering_meet in H. *)
(*       destruct H. rewrite covering_map in H. rewrite covering_map in H0. *)
(*       apply IHp in H. apply IHp in H0. apply funext. intro d. *)
(*       assert (I_end_map (S p) b = (I_end_map p b) o (degen_c (last_finset p))). *)
(*       apply funext. intro d'. unfold fcompose. apply funext. intro x. *)
(*       reflexivity. rewrite H1. clear H1. *)
(*       remember (d (last_finset p)) as dSp. destruct dSp. *)
(*       * rewrite H. unfold fcompose. apply funext. intros [k Hk]. *)
(*         match goal with *)
(*         | |- i ?F _ = i d _ => assert (F = d) *)
(*         end.  *)
(*         apply funext. intros [x Hx]. unfold degen_c. unfold last_finset. destruct (lt_eq_lt_dec x p) as [[H1 | H1] | H1]. *)
(*         -- repeat f_equal. *)
(*            apply Peano_dec.le_unique. *)
(*         -- destruct H1. unfold last_finset in HeqdSp. rewrite HeqdSp. repeat f_equal. apply Peano_dec.le_unique. *)
(*         -- easy. *)
(*         -- rewrite H1. reflexivity. *)
(*       * rewrite H0. unfold fcompose. apply funext. intros [k Hk]. *)
(*         match goal with *)
(*         | |- i ?F _ = i d _ => assert (F = d) *)
(*         end.  *)
(*         apply funext. intros [x Hx]. unfold degen_c. unfold last_finset. destruct (lt_eq_lt_dec x p) as [[H1 | H1] | H1]. *)
(*         -- repeat f_equal. *)
(*            apply Peano_dec.le_unique. *)
(*         -- destruct H1. unfold last_finset in HeqdSp. rewrite HeqdSp. repeat f_equal. apply Peano_dec.le_unique. *)
(*         -- easy. *)
(*         -- rewrite H1. reflexivity. *)
(*     +  apply covering_meet. apply conj. *)
(*        * fold @extremity. *)
(*          apply covering_map. apply IHp. rewrite <- H. apply funext. intro d. apply funext. intro k. reflexivity. *)
(*        * fold @extremity. *)
(*          apply covering_map. apply IHp. rewrite <- H. apply funext. intro d. apply funext. intro k. reflexivity. *)
(* Defined. *)


(* Run TemplateProgram (tImplementTC realize_TC "extremity_F0_TC" "F0" (forall (i : I), F)). *)
(* Next Obligation. *)
(*   unfold Fᵗ, Fᵗ_obligation_1. exact (extremity false (i p id)). *)
(* Defined. *)


(* Run TemplateProgram (tImplementTC extremity_F0_TC "natf_F0_TC" "natf_F0" (forall i : I, nati i -> natf (F0 i))). *)
(* Next Obligation. *)
(*   unfold natfᵗ, natfᵗ_obligation_1. *)
(*   intros. unfold F0ᵗ, F0ᵗ_obligation_1. *)
(*   simpl_comp. unfold extremity. unfold natiᵗ, Forcing_I.natiᵗ_obligation_1 in H. *)
(*     specialize (H p id p1 α1). simpl_comp_hyp. rewrite <- H.  *)
(*     destruct (eq_decidable_cube (i p id) (I_end_map p false)). *)
(*   - simpl.  *)
(*     destruct (eq_decidable_cube (α1 ô i p id) (I_end_map p1 false)). *)
(*     + simpl. apply conj. left.  intro k. intro H'. intro x. now left. easy.  *)
(*     + rewrite e in e0. destruct e0. destruct H0.  unfold compose, fcompose, I_end_map in H0. easy. *)
(*   - easy. *)
(* Defined. *)

(* Run TemplateProgram (TC <- Translate natf_F0_TC "iff" ;;  *)
(*                      tmDefinition "iff_TC" TC). *)

(* Run TemplateProgram (tImplementTC iff_TC "F0_correct_TC" "F0_correct" (forall (i : I), realize (F0 i) <-> (i = I0))). *)
(* Next Obligation. *)
(*   split. *)
(*   - intros. apply eq_is_eq. apply funext_dep. intro p1. apply funext_dep. intro α1. simpl_comp. *)
(*     unfold realizeᵗ, realizeᵗ_obligation_1 in H. *)
(*     unfold F0ᵗ, F0ᵗ_obligation_1 in H. specialize (H p1 α1). *)
(*     simpl_comp_hyp. rewrite extremity_correct in H. easy. *)
(*   - intros. simpl_comp. simpl_comp_hyp. specialize (H p0 id).  *)
(*     unfold realizeᵗ, realizeᵗ_obligation_1.  *)
(*     unfold F0ᵗ, F0ᵗ_obligation_1. apply extremity_correct. unfold I0ᵗ, Forcing_I.I0ᵗ_obligation_1 in H. unfold I_end in H. *)
(*     change (I_end_map p0 false) with ((fun (p : nat) (_ : p0 ~> p) => I_end_map p false) p0 id). destruct H. reflexivity. *)
(* Defined. *)



(* Definition realize_dec (f : F) := (realize f) \/ (~ realize f). *)



(* Run TemplateProgram (TC <- Translate F0_correct_TC "not" ;; *)
(*                         tmDefinition "not_TC" TC). *)

(* Run TemplateProgram (TC <- Translate not_TC "realize_dec" ;; *)
(*                         tmDefinition "real_dec_TC" TC). *)



(* (* Run TemplateProgram (tImplementTC F0_correct_TC "join_simon_TC" "join_simon" (forall A (φ φ' : F) *) *)
(* (*            (f : realize φ -> A) (g : realize φ' -> A) (H : forall u v, f u = g v),  realize φ \/ realize φ' -> A)). *) *)
(* (* Next Obligation. *) *)
(* (*   simpl_comp. simpl_comp_hyp. *) *)
(* (*   specialize (H0 p id). destruct H0. *) *)
(* (*   - remember (f p id) as fp. simpl_comp_hyp. apply fp. exact H0. *) *)
(* (*   - remember (g p id) as gp. simpl_comp_hyp. apply gp. exact H0. *) *)
(* (* Defined. *) *)

(* (* Definition left_or A B (x : A) :  A \/ B := or_introl x. *) *)

(* (* Run TemplateProgram (TC <- ImplementExisting join_simon_TC "left_or" ;; *) *)
(* (*                         tmDefinition "or_introl_TC" TC). *) *)
(* (* Next Obligation. *) *)
(* (*   apply or_introlᵗ. exact x. *) *)
(* (* Defined. *) *)

(* (* Run TemplateProgram (tImplementTC join_simon_TC "join_l_TC" "join_l" *) *)
(* (*                                   (forall {A} {φ φ' : F} (f : realize φ -> A) (g : realize φ' -> A) (H : forall u v, f u = g v) (u : realize φ), *) *)
(* (*                                       join_simon A φ φ' f g H (left_or _ _ u) = f u)). *) *)


(* (* Run TemplateProgram (tImplementTC real_dec_TC "test_TC" "test" (forall f : F, natf f ->  realize_dec f)). *) *)
(* (* Next Obligation. *) *)
(* (*   unfold realize_decᵗ. unfold realizeᵗ, realizeᵗ_obligation_1. simpl_comp. *) *)
(* (*   unfold extremity. unfold  natiᵗ, natiᵗ_obligation_1 in H. *) *)
(* (*   destruct (covering_dec (f p id)). *) *)
(* (*   - apply or_introlᵗ. intros. simpl_comp. *) *)
(* (*     specialize (H p id p0 α). simpl_comp_hyp. unfold natfᵗ, natfᵗ_obligation_1 in H. exact (restrict_covering H c). *) *)
(* (*   - apply or_introrᵗ. intros. simpl_comp. *) *)
(* (*     unfold natfᵗ, natfᵗ_obligation_1 in H. *) *)
(* (*     unfold notᵗ. intro. *) *)
(* (*     simpl_comp_hyp. *) *)
(* (*     (**** Impossible ??***) *) *)
(* (*  Admitted. *) *)

    

(* (* Run TemplateProgram (tImplementTC real_dec_TC "test_TC" "test" (forall i : I, nati i ->  realize_dec (F0 i))). *) *)
(* (* Next Obligation. *) *)
(* (*   unfold realize_decᵗ. unfold realizeᵗ, realizeᵗ_obligation_1. simpl_comp. unfold F0ᵗ. unfold F0ᵗ_obligation_1. *) *)
(* (*   unfold extremity. unfold  natiᵗ, natiᵗ_obligation_1 in H. *) *)
(* (*   destruct (eq_decidable_cube (i p id) (I_end_map p false)). *) *)
(* (*   - apply or_introrᵗ. intros. simpl_comp. *) *)
(* (*     specialize (H p id p0 α). *) *)
(* (*     simpl_comp_hyp. rewrite <- H. *) *)
(* (*     destruct (eq_decidable_cube (α ô i p id) (I_end_map p0 false)). *) *)
(* (*     + simpl. left. intro k. reflexivity. *) *)
(* (*     + destruct e0. destruct H0. rewrite e in H0. unfold fcompose, compose, I_end_map in H0. easy. *) *)
(* (*   - apply or_introlᵗ. unfold notᵗ. intros. simpl_comp_hyp. destruct e. destruct H1. *) *)
(* (*     specialize (H0 p0 id). simpl_comp_hyp. *) *)
(* (*     destruct (eq_decidable_cube (i p0 α) (I_end_map p0 false)). *) *)
(* (*     + specialize (H p id p0 α). simpl_comp_hyp. *) *)
(* (*       rewrite <- H in e. unfold compose, fcompose in e. unfold Iᵗ, Iᵗ_obligation_1 in i. *) *)
(* (*     (**** Impossible ??***) *) *)
(* (* Admitted. *) *)


(* Run TemplateProgram (tImplementTC F0_correct_TC "F1_TC" "F1" (forall (i : I), F)). *)
(* Next Obligation. *)
(*   unfold Fᵗ, Fᵗ_obligation_1. exact (extremity true (i p id)). *)
(* Defined. *)



(* Run TemplateProgram (tImplementTC F1_TC "F1_correct_TC" "F1_correct" (forall (i : I), realize (F1 i) <-> (i = I1))). *)
(* Next Obligation. *)
(*   split; intros. *)
(*   - apply eq_is_eq. apply funext_dep. intro p1. apply funext_dep. intro α1. simpl_comp. *)
(*     unfold realizeᵗ, realizeᵗ_obligation_1 in H. *)
(*     unfold F1ᵗ, F1ᵗ_obligation_1 in H. specialize (H p1 α1). *)
(*     simpl_comp_hyp. rewrite extremity_correct in H. easy. *)
(*   - specialize (H p0 id).  *)
(*     unfold realizeᵗ, realizeᵗ_obligation_1.  *)
(*     unfold F1ᵗ, F1ᵗ_obligation_1. apply extremity_correct. unfold I1ᵗ, Forcing_I.I1ᵗ_obligation_1 in H. unfold I_end in H. *)
(*     change (I_end_map p0 true) with ((fun (p : nat) (_ : p0 ~> p) => I_end_map p true) p0 id). destruct H. reflexivity. *)
(* Defined. *)

(* Run TemplateProgram (tImplementTC F1_correct_TC "F1_natf_TC" "F1_natf" (forall i : I, nati i -> natf (F1 i))). *)
(* Next Obligation. *)
(*   unfold natfᵗ, natfᵗ_obligation_1. *)
(*   intros. unfold F1ᵗ, F1ᵗ_obligation_1. *)
(*   simpl_comp. unfold extremity. unfold natiᵗ, Forcing_I.natiᵗ_obligation_1 in H. *)
(*   specialize (H p id p1 α1). simpl_comp_hyp. rewrite <- H.  *)
(*   destruct (eq_decidable_cube (i p id) (I_end_map p true)). *)
(*   - simpl.  *)
(*     destruct (eq_decidable_cube (α1 ô i p id) (I_end_map p1 true)). *)
(*     + simpl. apply conj. left.  intro k. intro H'. intro x. now left. easy.  *)
(*     + rewrite e in e0. destruct e0. destruct H0.  unfold compose, fcompose, I_end_map in H0. easy. *)
(*   - easy. *)
(* Defined. *)




(* (* Run TemplateProgram (tImplementTC cof_TC "ax5_TC" "ax5" (forall (i : I) (H : nati i), cof (i = I0) /\ cof (i = I1))). *) *)
(* (* Next Obligation. *) *)
(* (*   apply conjᵗ. *) *)
(* (*   - intros pz αz. specialize (H pz αz). unshelve refine (ex_intro _ _ _). (* unshelve refine (ex_intro _ _ _). *) *) *)
(* (*     + intros p0 α0. exact (extremity false (i p0 (α0 ô αz))). *) *)
(* (*     + intros p0 α0. split. *) *)
(* (*       * intro H1. apply eq_is_eq. apply (extremity_correct false (i p0 (α0 ô αz))) in H1. *) *)
(* (*         apply funext_dep. intro p1. apply funext. intro α1.  simpl. simpl_comp. *) *)
(* (*         change (α1 ô α0 ô αz) with (α1 ô α0 ô id ô (αz ô (id ô id))). *) *)
(* (*         rewrite <- (H _ (α1 ô α0)). simpl_comp. *) *)
(* (*         change (α1 ô α0 ô i pz αz) with (α1 ô (α0 ô i pz (αz ô id ô id ô id))). *) *)
(* (*         rewrite H. simpl_comp.  rewrite <- H1. *) *)
(* (*         now compute. *) *)
(* (*       * intro Heq. rewrite extremity_correct. *) *)
(* (*         assert ((fun (p2 : nat) (α1 : p0 ~> p2) => i p2 (α1 ô α0 ô αz)) = (fun (p2 : nat) (α1 : p0 ~> p2) => I0ᵗ p2)). *) *)
(* (*         destruct Heq. apply funext_dep. intro p2. apply funext. intro α1. reflexivity. *) *)
(* (*         apply (TFUtils.ap (fun f => f p0)) in H0. simpl in H0. *) *)
(* (*         apply (TFUtils.ap (fun f => f id)) in H0. simpl in H0. simpl_comp_hyp. rewrite H0. simpl. reflexivity. *) *)
(* (*   - intros pz αz. specialize (H pz αz). unshelve refine (ex_intro _ _ _). *) *)
(* (*     + intros p0 α0. exact (extremity true (i p0 (α0 ô αz))). *) *)
(* (*     + intros p0 α0. split. *) *)
(* (*       * intro H1. apply eq_is_eq. apply (extremity_correct true (i p0 (α0 ô αz))) in H1. *) *)
(* (*         apply funext_dep. intro p1. apply funext. intro α1.  simpl. simpl_comp. *) *)
(* (*         change (α1 ô α0 ô αz) with (α1 ô α0 ô id ô (αz ô (id ô id))). *) *)
(* (*         rewrite <- (H _ (α1 ô α0)). simpl_comp. *) *)
(* (*         change (α1 ô α0 ô i pz αz) with (α1 ô (α0 ô i pz (αz ô id ô id ô id))). *) *)
(* (*         rewrite H. simpl_comp.  rewrite <- H1. *) *)
(* (*         now compute. *) *)
(* (*       * intro Heq. rewrite extremity_correct. *) *)
(* (*         assert ((fun (p2 : nat) (α1 : p0 ~> p2) => i p2 (α1 ô α0 ô αz)) = (fun (p2 : nat) (α1 : p0 ~> p2) => I1ᵗ p2)). *) *)
(* (*         destruct Heq. apply funext_dep. intro p2. apply funext. intro α1. reflexivity. *) *)
(* (*         apply (TFUtils.ap (fun f => f p0)) in H0. simpl in H0. *) *)
(* (*         apply (TFUtils.ap (fun f => f id)) in H0. simpl in H0. simpl_comp_hyp. rewrite H0. simpl. reflexivity. *) *)
(* (* Defined. *) *)


    
  
(* (* Fixpoint ext {p : nat} (b : bool) (i : cube p -> cube 1) {struct p}: face_lattice p.   *) *)

(* (* Theorem extremity_correct {p : nat} (b : bool) (i : cube p -> cube 1) : *) *)
(* (*   covering (extremity b i) <-> I_end_map p b = i. *) *)

(* (* This thing cannot work, for in our vision of presheaves a disjunction isnt sheaf-like *) *)
(* (* Run TemplateProgram (tImplementTC ax5_1_TC "ax6_TC" "ax6" (forall (φ ψ : Prop) (Hφ : cof φ) (Hψ : cof ψ), cof (φ \/ ψ))). *) *)

(* Run TemplateProgram (tImplementTC F1_correct_TC "For_TC" "For" (F -> F -> F)). *)
(* Next Obligation. *)
(*   exact (join_faces (X p id) (X0 p id)). *)
(* Defined. *)

(* Run TemplateProgram (tImplementTC For_TC "For_correct_TC" "For_correct" *)
(*                                   (forall f g : F, natf f -> natf g -> realize (For f g) <-> realize f \/ realize g)). *)
(* Next Obligation. *)
(*   split; intros. *)
(*   - unfold realizeᵗ, realizeᵗ_obligation_1 in *. unfold Forᵗ, Forᵗ_obligation_1 in H1. *)
(*     specialize (H1 p0 id). apply covering_join in H1. destruct H1. *)
(*     + apply or_introlᵗ. intros. simpl_comp. simpl_comp_hyp. *)
(*       unfold natfᵗ, natfᵗ_obligation_1 in H. refine (restrict_covering _ _). *)
(*       * exact (H p0 α p1 α0). *)
(*       * exact H1. *)
(*     + apply or_introrᵗ. intros. simpl_comp. simpl_comp_hyp. unfold natfᵗ, natfᵗ_obligation_1 in H0. refine (restrict_covering _ _). *)
(*       * exact (H0 p0 α p1 α0). *)
(*       * exact H1. *)
(*   -  unfold realizeᵗ, realizeᵗ_obligation_1 in *. *)
(*      unfold Forᵗ, Forᵗ_obligation_1. simpl_comp. simpl_comp_hyp. *)
(*      apply covering_join.  specialize (H1 p0 id). destruct H1. *)
(*      + apply or_introl. exact (H1 p0 id). *)
(*      + apply or_intror. exact (H1 p0 id). *)
(* Defined. *)


(* Run TemplateProgram (tImplementTC For_correct_TC "For_natf_TC" "For_natf" (forall f g : F, natf f -> natf g -> natf (For f g))). *)
(* Next Obligation. *)
(*   unfold natfᵗ, natfᵗ_obligation_1 in *. intros. unfold Forᵗ, Forᵗ_obligation_1. simpl. simpl_comp; simpl_comp_hyp. *)
(*   specialize (H p id p1 α1). specialize (H0 p id p1 α1). simpl_comp. simpl_comp_hyp. *)
(*   apply restrict_join'. apply conj; apply restrict_join; easy. *)
(* Defined. *)

                           
  
(* Run TemplateProgram (tImplementTC For_natf_TC "Fand_TC" "Fand" (F -> F -> F)). *)
(* Next Obligation. *)
(*   exact (meet_faces (X p id) (X0 p id)). *)
(* Defined. *)

(* Run TemplateProgram (tImplementTC Fand_TC "Fand_correct_TC" "Fand_correct" (forall f g : F, realize (Fand f g) <-> realize f /\ realize g)). *)
(* Next Obligation. *)
(*   split; intros. *)
(*   - unfold realizeᵗ, realizeᵗ_obligation_1 in *. unfold Fandᵗ, Fandᵗ_obligation_1 in H. *)
(*     apply conjᵗ; simpl_comp; simpl_comp_hyp. *)
(*     + intros. specialize (H p1 α0). *)
(*       apply covering_meet in H. destruct H. exact H. *)
(*     + intros. specialize (H p1 α0). *)
(*       apply covering_meet in H. destruct H. exact H0. *)
(*   -   unfold realizeᵗ, realizeᵗ_obligation_1 in *. *)
(*       unfold Fandᵗ, Fandᵗ_obligation_1. simpl_comp. simpl_comp_hyp. *)
(*       apply covering_meet. specialize (H p0 id). destruct H. apply conj.  *)
(*       +  exact (H p0 id). *)
(*       +  exact (H0 p0 id). *)
(* Defined. *)

(* Run TemplateProgram (tImplementTC Fand_correct_TC "Fand_natf_TC" "Fand_natf" (forall f g : F, natf f -> natf g -> natf (Fand f g))). *)
(* Next Obligation. *)
(*   unfold natfᵗ, natfᵗ_obligation_1 in *. intros. unfold Fandᵗ, Fandᵗ_obligation_1. simpl. simpl_comp; simpl_comp_hyp. *)
(*   specialize (H p id p1 α1). specialize (H0 p id p1 α1). simpl_comp. simpl_comp_hyp. *)
(*   apply restrict_meet. split; apply restrict_meet'. *)
(*   - left. exact H. *)
(*   - right. exact H0. *)
(* Defined. *)


(* Run TemplateProgram (tImplementTC Fand_natf_TC "Fforall_TC" "Fforall" ((I -> F) -> F)). *)
(* Next Obligation. *)
(*   specialize (X p id). apply forall_faces. intro k. apply X. intros. unfold Iᵗ, Forcing_I.Iᵗ_obligation_1. exact (α ô k). *)
(* Defined. *)
 

(* Run TemplateProgram (tImplementTC Fforall_TC "Fforall_correct_TC" "Forall_correct" *)
(*                                   (forall f : I -> F, realize (Fforall f) <-> forall i : I, nati i -> realize (f i))). *)
(* Next Obligation. *)
(*   split. *)
(*   - intros. *)
(*     unfold realizeᵗ, realizeᵗ_obligation_1 in *. simpl_comp. *)
(*     specialize (H p0 id). simpl_comp_hyp. unfold Fforallᵗ, Fforallᵗ_obligation_1 in H. *)
(*     rewrite forall_faces_covering in H. simpl_comp_hyp. *)
(*     specialize (H (i p0 id)). *)
(*     unfold natiᵗ, Forcing_I.natiᵗ_obligation_1 in H0. *)
(*     assert ((fun (p1 : nat) (α0 : p0 ~> p1) => i p1 (α0 ô id)) = (fun (p1 : nat) (α : p0 ~> p1) => α ô i p0 id)). *)
(*     { apply funext_dep. intro p1. apply funext_dep. intro α1. simpl_comp. *)
(*       specialize (H0 _ id _ α1). simpl_comp_hyp. easy. *)
(*     } rewrite H1. exact H. *)
(*   - intros. unfold realizeᵗ, realizeᵗ_obligation_1 in *. simpl_comp. simpl_comp_hyp. *)
(*     unfold Fforallᵗ, Fforallᵗ_obligation_1. rewrite forall_faces_covering. *)
(*     intro i. specialize (H p0 id). simpl_comp_hyp. simpl_comp. *)
(*     match goal with *)
(*     | |- covering (f p0 α (fun p1 α0 => @?k p1 α0)) => specialize (H k) *)
(*     end. *)
(*     apply H. *)
(*     intros. *)
(*     unfold natiᵗ, Forcing_I.natiᵗ_obligation_1. reflexivity. *)
(* Defined. *)

(* Run TemplateProgram (tImplementTC Fforall_correct_TC "Fforall_natf_TC" "Fforall_natf" *)
(*                                   (forall f : I -> F, (forall i : I, natf (f i)) -> natf (Fforall f))). *)
(* Next Obligation. *)
(*   unfold natfᵗ, natfᵗ_obligation_1 in *. *)
(*   intros. simpl_comp; simpl_comp_hyp. *)
(*   unfold Fforallᵗ, Fforallᵗ_obligation_1. unfold forall_faces. simpl_comp. *)
(*   destruct (forall_covering_dec (fun k : 1 ~> p => f p id (fun (p0 : nat) (α : p ~> p0) => α ô k))). *)
(*   - destruct (forall_covering_dec (fun k : 1 ~> p1 => f p1 α1 (fun (p0 : nat) (α : p1 ~> p0) => α ô k))). *)
(*     + simpl. split. *)
(*       * left. unfold restricts_constraint_aux. intros x Hf k. left. reflexivity. *)
(*       * easy. *)
(*     + specialize (H p1 α1). simpl_comp_hyp. *)
(*       assert (forall i : 1 ~> p1, covering (f p1 α1 (fun (p0 : nat) (α : p1 ~> p0) => α ô i))). *)
(*       { intro i. specialize (H (fun _ j => j ô i)). simpl_comp_hyp. *)
(*         (** No clue **) *)
  
(* Admitted. *)


(* Run TemplateProgram (tImplementTC Fand_natf_TC "Fforall_TC" "Fforall" ((J -> F) -> F)). *)
(* Next Obligation. *)
(*   specialize (X p id). apply forall_faces. intro k. apply X. intros. unfold Jᵗ. unshelve refine (existTᵗ _ _ _ _ _). *)
(*   - intros. exact (α0 ô α ô k). *)
(*   -  intros.  unfold natiᵗ, natiᵗ_obligation_1. intros. reflexivity. *)
(* Defined. *)
 

(* Run TemplateProgram (tImplementTC Fforall_TC "Fforall_correct_TC" "Forall_correct" *)
(*                                   (forall f : J -> F, realize (Fforall f) <-> forall i : J, natj i -> realize (f i))). *)
(* Next Obligation. *)
(*   split. *)
(*   - intros. *)
(*     unfold realizeᵗ, realizeᵗ_obligation_1 in *. simpl_comp. *)
(*     specialize (H p0 id). simpl_comp_hyp. unfold Fforallᵗ, Fforallᵗ_obligation_1 in H. *)
(*     rewrite forall_faces_covering in H. simpl_comp_hyp. *)
(*     remember (i p0 id) as ip0. *)
(*     destruct ip0. specialize (H (x p0 id)). *)
(*     assert ((fun (p1 : nat) (α : p0 ~> p1) => *)
(*             existTᵗ p1 (fun (p : nat) (_ : p1 ~> p) => Iᵗ p) *)
(*               (fun (p : nat) (_ : p1 ~> p) (i : forall p0 : nat, p ~> p0 -> Iᵗ p0 p0 id) => *)
(*                natiᵗ p (fun (p0 : nat) (α1 : p ~> p0) => i p0 (α1 ô id))) (fun (p2 : nat) (α0 : p1 ~> p2) => α0 ô α ô x p0 id) *)
(*               (fun (p2 : nat) (α0 : p1 ~> p2) (p3 : nat) (α1 : p2 ~> p3) => eq_refl)) = (fun (p1 : nat) (α0 : p0 ~> p1) => i p1 (α0 ô id))). *)
(*     { apply funext_dep. intro p1. apply funext_dep. intro α1. simpl_comp. *)
(*       unfold natjᵗ, natjᵗ_obligation_1 in H0. specialize (H0 p0 id p1 α1). simpl_comp_hyp. rewrite H0.  *)
(*       unshelve refine (dep_eq _ _ _ _ _ _). *)
(*       +  apply funext_dep. intro p2. apply funext_dep. intro α0. rewrite <- Heqip0. unfold natiᵗ, natiᵗ_obligation_1 in n. *)
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
(*     destruct H1. exact H. *)
(*   - intros. unfold realizeᵗ, realizeᵗ_obligation_1 in *. simpl_comp. simpl_comp_hyp. *)
(*     unfold Fforallᵗ, Fforallᵗ_obligation_1. rewrite forall_faces_covering. *)
(*     intro i. specialize (H p0 id). simpl_comp_hyp. simpl_comp. *)
(*     match goal with *)
(*     | |- covering (f p0 α (fun p1 α0 => @?k p1 α0)) => specialize (H k) *)
(*     end. *)
(*     apply H. *)
(*     intros. *)
(*     unfold natjᵗ, natjᵗ_obligation_1. reflexivity. *)
(* Defined. *)
      
                         

(* Run TemplateProgram (tImplementTC ax5_TC "ax6_TC" "ax6" (forall ϕ ψ : Prop, cof ϕ -> cof ψ -> cof (ϕ /\ ψ))). *)
(* Next Obligation. *)


(* (* unshelve refine (ex_intro _ _ _). specialize (H p id). specialize (H0 p id).  *) *)
(*   (* - intros p0 α0. unfold cofᵗ in H, H0. unfold cofᵗ_obligation_1 in H, H0. simpl_comp_hyp. *) *)
(* Admitted. *)




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

Theorem covering_assumption {p : nat} {f : face_lattice p} (c : covering f) : covering_dec f = left c.
Proof.
  destruct (covering_dec f).
  - apply f_equal. apply proof_irr.
  - absurd (covering f). exact n. exact c.
Qed.

Theorem noncovering_assumption {p : nat} {f : face_lattice p} (c : ~ covering f) : covering_dec f = right c.
Proof.
  destruct (covering_dec f).
  - absurd (covering f). exact c. exact c0.
  - apply f_equal. apply proof_irr.
Qed.

Print F. 
Inductive Fᵗ (p : 𝐂_obj) : Type :=
    F1ᵗ :  (forall p0 : 𝐂_obj, (p ~> p0) -> Iᵗ p0 p0 id) -> Fᵗ p
  | F0ᵗ :  (forall p0 : 𝐂_obj, (p ~> p0) -> Iᵗ p0 p0 id) -> Fᵗ p
  | Forᵗ : (forall p0 : 𝐂_obj, (p ~> p0) -> Fᵗ p0) ->
           (forall p0 : 𝐂_obj, (p ~> p0) -> Fᵗ p0) ->
           Fᵗ p
  | Fandᵗ : (forall p0 : 𝐂_obj, (p ~> p0) -> Fᵗ p0) ->
            (forall p0 : 𝐂_obj, (p ~> p0) -> Fᵗ p0) ->
            Fᵗ p 
  | Fforallᵗ : (forall p0 : 𝐂_obj, (p ~> p0) -> (forall p1 : nat, (p0 ~> p1) -> Iᵗ p1 p1 id) -> Fᵗ p0)
               -> Fᵗ p.

 

Run TemplateProgram (TC1 <- tAddExistingInd isEq_TC "Top.F" "Fᵗ" ;;
                          tmDefinition "Ft_TC" TC1).






Run TemplateProgram (tImplementTC Ft_TC "covers_TC" "covers" (F -> Prop)).
Next Obligation.
  specialize (X p id).
  induction X.
  - exact (i p0 α = I1ᵗ p0).
  - exact (i p0 α = I0ᵗ p0).
  - exact ((X p0 α id) \/ (X0 p0 α id)).
  - exact ((X p0 α id) /\ (X0 p0 α id)).
  - specialize (X p0 α).
    exact (forall i, X i id).
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

  
Run TemplateProgram (tImplementTC Ft_TC "adm_TC" "adm"
                                  (Prop -> Prop)).
Next Obligation.
  exact (dec (X p id p0 α)). (** could change that in many ways **)
Defined.

Run TemplateProgram (tImplementTC adm_TC "natp_TC" "natp"
                                  (Prop -> Prop)).
Next Obligation.
  exact (forall q β, X p0 α p0 id -> X q (β ô α) q id).
Defined.



Run TemplateProgram (tImplementTC natp_TC "ax9_TC" "ax9"
                                  (forall (ϕ : Prop) (Hnat : natp ϕ) (Hcof : adm ϕ) 
                                     (A : ϕ -> Type) (B : Type) (s : forall u : ϕ, A u ≅ B),
                                      Σ (B' : Type) (s' : B' ≅ B), (forall u : ϕ, A u = B'))).
Next Obligation.
  unshelve refine (existTᵗ _ _ _ _ _);  unfold admᵗ, admᵗ_obligation_1 in Hcof; unfold dec in Hcof; unfold natpᵗ, natpᵗ_obligation_1 in Hnat.
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