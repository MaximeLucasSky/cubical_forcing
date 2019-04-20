Require Import BasicsMisc.
(* Require Import Sprop_utils. *)
Require Import Hott_lemmas.
Require Import Simple_arithmetic.
Require Import Cubes.
Require Import Monotonicity.

(** Cartesian structure *)

(* based on the decidability part. This actually only requires the category of cubes having contractions *)

Definition fuse_cube_maps {a b c : nat} : (cube a -> cube b) * (cube a -> cube c) -> (cube a -> cube (b + c)).
  intros [f g] d [x p].
  destruct (le_lt_dec b x).
  - assert (x - b < c). apply le_plus_n with (p := b). rewrite add_S.
    rewrite <- Minus.le_plus_minus. exact p. exact l.
    apply (g d). exists (x - b). exact H.
  - apply (f d). exists x. exact l.
Defined.

Definition fuse_arrows {a b c : nat} : (a ~> c) * (b ~> c) -> (a + b ~> c) := fuse_cube_maps.

Definition split_cube_map {a b c : nat} : (cube a -> cube (b + c)) -> (cube a -> cube b) * (cube a -> cube c).
  intro f. split.
  - intros d [x p]. apply (f d). exists x. easy.
  - intros d [x p]. apply (f d). exists (b + x). unfold lt. rewrite <- add_S.
    apply Plus.plus_le_compat_l. exact p.
Defined.

Definition split_arrow {a b c : nat} : (a + b ~> c) -> (a ~> c) * (b ~> c) := split_cube_map.
 

Theorem cartesian_lemma1 {a b c : nat} : forall f : cube a -> cube (b + c), fuse_cube_maps (split_cube_map f) = f.
  intro f.
  apply funext. intro d.
  apply funext. intros [x p].
  simpl. destruct (le_lt_dec b x).
  - assert (forall p' : b + (x - b) < b + c, exist (fun m : nat => m < b + c) (b + (x - b)) p' = exist (fun m : nat => m < b + c) x p).
    rewrite <- Minus.le_plus_minus. intro p'. rewrite (Peano_dec.le_unique (S x) (b + c) p p'). reflexivity.
    exact l.
    rewrite H. reflexivity.
  - erewrite (Peano_dec.le_unique _ _ (Plus.lt_plus_trans x b c l) p). reflexivity.
Qed.

Theorem cartesian_lemma2 {a b c : nat}
  : forall (f : cube a -> cube b) (g : cube a -> cube c), split_cube_map (fuse_cube_maps (f, g)) = (f, g).
  intros f g. apply injective_projections.
  - apply funext. intro d.
    apply funext. intros [x p].
    simpl. destruct (le_lt_dec b x).
    + assert False. easy. inversion H.
    + erewrite (Peano_dec.le_unique _ _ l p). reflexivity.
  - apply funext. intro d.
    apply funext. intros [x p].
    simpl. destruct (le_lt_dec b (b + x)).
    + assert (forall p' : b + x - b < c, exist (fun m : nat => m < c) (b + x - b) p' = exist (fun m : nat => m < c) x p).
      replace (b + x - b) with x. intro p'. erewrite (Peano_dec.le_unique _ _ p p'). reflexivity.
      easy.
      rewrite H. reflexivity.
    + assert False. easy. inversion H.
Qed.

Theorem cartesian_iso1 {a b c : nat} : fuse_arrows o split_arrow = fun x : a + b ~> c => x.
Proof.
  apply funext. 
  exact (cartesian_lemma1).
Qed.

Theorem cartesian_iso2 {a b c : nat} : split_arrow o fuse_arrows = fun x : (a ~> c) * (b ~> c) => x.
Proof.
  apply funext.  intros [f g]. revert g. revert f. exact cartesian_lemma2.
Qed. 