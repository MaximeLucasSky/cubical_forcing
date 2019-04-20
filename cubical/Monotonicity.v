Require Import BasicsMisc.
Require Import Hott_lemmas.
Require Import Simple_arithmetic.
Require Import Cubes.

(** Decidability of a function being cubic *)

(* uses the fact that for the full category of cubes, being admissible is the same as being monotone *)
(* WIP *)

Definition zero_finset (p : nat) : finset (S p).
  exists 0. easy.
Defined.

Definition unique : cube 0.
  unfold cube. unfold finset. intros [m H]. apply pos_ge_0 in H. inversion H.
Defined.

Definition extend_cube {a : nat} (c : cube a) (b : bool) : cube (S a).
  intros [i p]. destruct i.
  - exact b.
  - apply le_S_n in p. apply c. exists i. exact p.
Defined.

Definition restr_map {a : nat} (f : cube (S a) -> cube 1) (b : bool) : cube a -> cube 1 :=
  fun x : cube a => f (extend_cube x b).


Definition fuse_cube {a b : nat} : (cube a) * (cube b) -> cube (a + b).
  intros [c d] [p i]. destruct (Compare_dec.le_lt_dec a p).
  - assert (p - a < b). easy.
    apply d. exists (p - a). exact H.
  - apply c. exists p. exact l.
Defined.

Definition split_cube {a b : nat} : cube (a + b) -> (cube a) * (cube b).
  intro c. split.
  - intros [x p]. apply c. exists x. easy.
  - intros [x p]. apply c. exists (x + a). easy.
Defined.


(** dup_word, dup_map, dup_aux1 
    maps 2^n -> 2^(2n) that duplicate input *)

Definition dup_map (a : nat) : cube a -> cube (a + a).
  intros d [x Hx].
  destruct (le_lt_dec a x).
  - apply d. exists (x - a). apply le_plus_n with (p := a). rewrite add_S. rewrite <- Minus.le_plus_minus.
    + exact Hx.
    + exact l.
  - apply d. exists x. exact l.
Defined.



Import PeanoNat.
(** tensor_word, tensor_map, tensor_adm 
    make a map 2^(a+b) -> 2^(c+d) from two maps 2^a -> 2^c and 2^b -> 2^d *)

Lemma transport_finset {a b x : nat} {e : a = b} (f : nat -> nat) {H : x < f a} :
  transport (fun X : nat => finset (f X)) e (exist (fun m => m < f a) x H) = exist _ x (transport (fun m => x < f m) e H).
Proof.
  destruct e. reflexivity.
Qed.

Definition tensor_map {a b a' b'} (w : cube a -> cube b) (w' : cube a' -> cube b') : cube (a + a') -> cube (b + b').
  intros d [x Hx].
  destruct (le_lt_dec b x).
  - apply w'.
    + intros [y Hy]. apply d. exists (a + y). easy. 
    + exists (x - b). easy.  
  - apply w.
    + intros [y Hy]. apply d. exists y. apply Nat.lt_lt_add_r. exact Hy.
    + exists x. exact l.
Defined.

Lemma transport_cube {a b : nat} {e : a = b} (c : cube a) (d : finset b)
  : transport cube e c d = c (transport finset (sym e) d).
Proof.
  destruct e. reflexivity.
Qed.

Lemma transport_cube' {a b x : nat} {e : a = b} (c : cube a) (H : x < b)
  : transport cube e c (exist (fun m => m < b) x H) = c (exist _ x (transport (fun m => x < m) (sym e) H)).
Proof.
  destruct e. reflexivity.
Qed.




(** and/or maps *)


Definition binary_and_map : cube 2 -> cube 1.
  intros d x. apply andb.
  - apply d. exact (zero_finset 1).
  - apply d. exists 1. easy.
Defined.


Definition binary_or_map : cube 2 -> cube 1.
  intros d x. apply orb.
  - apply d. exact (zero_finset 1).
  - apply d. exists 1. easy.
Defined.


(** simpl_word, simpl_map, simpl_adm
    combine two maps f, g : 2^n -> 2 as h(x, …) = (f(…) and x) or g(…) *)

Definition simpl_map {a : nat} (f g : cube a -> cube 1) : cube (S a) -> cube 1.
  intros d x. apply orb.
  - apply andb.
    + apply f.
      * apply degen_c.
        -- exact (zero_finset a).
        -- exact d.
      * exact x.
    + apply d. exact (zero_finset a).
  - apply g.
    + apply degen_c.
      * exact (zero_finset a).
      * exact d.
    + exact x.
Defined.


(* simpl can decompose monotone maps *)



(** now using simpl, we can recover the word for a monotone function
    with only 1 output *)




(** * TODO : do the same with multiple outputs *)
