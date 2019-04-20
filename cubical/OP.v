Axiom J : Type.
Axiom J0 J1 : J.
Axiom ax1 : forall (φ : J -> Prop), ((forall i : J, φ i \/ (φ i -> False)) -> (forall i : J, φ i) \/ (forall i : J, φ i -> False)).
Axiom ax2 : (J0 = J1 -> False).
Axiom meet join: J -> J -> J.

Notation "a ⊓ b" := (meet a b) (at level 65, left associativity).
Notation "a ⊔ b" := (join a b) (at level 65, left associativity).

Axiom ax3 : forall i : J, J0 ⊓ i = J0 /\ i ⊓ J0 = J0 /\ J1 ⊓ i = i /\ i ⊓ J1 = i.
Axiom ax4 : forall i : J, J0 ⊔ i = i /\ i ⊔ J0 = i /\ J1 ⊔ i = J1 /\ i ⊔ J1 = J1.

Axiom cof : Prop -> Prop.

Axiom ax5 : forall i : J, cof (i = J0) /\ cof (i = J1).
Axiom ax6 : forall ϕ ψ : Prop, cof ϕ -> cof ψ -> cof (ϕ \/ ψ).
Axiom ax7 : forall ϕ ψ : Prop, cof ϕ -> (ϕ -> cof ψ) -> cof (ϕ /\ ψ).
Axiom ax8 : forall ϕ : J -> Prop, (forall i : J, cof (ϕ i)) -> cof (forall i : J, ϕ i).



Arguments existT {_ _} _.

Notation "'Σ' x .. y , P" := (sigT (fun x => .. (sigT (fun y => P)) .. ))
                            (at level 200, x binder, y binder, right associativity).
Notation "( x ; .. ; y ; z )" := (existT x (.. (existT y z) ..)).



Definition fcompose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C :=
  fun x : A => f (g x).

Notation "f 'o' g" := (fcompose f g) (at level 50, left associativity).

Definition isEquiv (A B : Type) : Type :=
  Σ (f : A -> B) (g : B -> A), (f o g = fun x => x) /\ (g o f = fun x => x).

Notation "A ≅ B" := (isEquiv A B) (at level 65, left associativity).

Axiom ax9 : forall (ϕ : Prop) (H : cof ϕ) (A : ϕ -> Type) (B : Type) (s : forall u : ϕ, (A u ≅ B)), Σ (B' : Type) (s' : B' ≅ B), (forall u : ϕ, A u = B') .

Definition Cof : Type := { ϕ : Prop | cof ϕ }.

Definition Cofib  (A B : Type) : Type := {m : A -> B