Require Import String.
Require Import List.
Require Import Omega.

Require Import Template.monad_utils
        Template.Ast
        Template.AstUtils
        Template.TemplateMonad
        Template.LiftSubst
        Template.Checker
        Template.Typing
        Template.Induction.

Require Import Translations.translation_utils.

Require Import Forcing.TemplateForcing
        Forcing.translation_utils_bis.

Require Import FunctionalExtensionality.

Set Primitive Projections.



(* composition *)

Definition fcompose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C :=
  fun x : A => f (g x).

Notation "f 'o' g" := (fcompose f g) (at level 50, left associativity).




(* axioms *)

Definition funext {A B : Type} := @functional_extensionality A B.
Definition funext_dep {A : Type} {B : A -> Type} := @functional_extensionality_dep A B.
Definition proof_irr {A : Prop} {a b : A} : a = b. Admitted.
Definition admitok : False. Admitted. (* this one is only temporary *)

