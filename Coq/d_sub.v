Require Export Arith.
Require Import List.
Require Import Nat.
Require Import CpdtTactics.
Require Import Coq.Logic.FunctionalExtensionality.

(**
Preliminary Tactics
 *)
Ltac notHyp P :=
  match goal with
  | [ _ : P |- _ ] => fail 1
  | _ =>
    match P with
    | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
    | _ => idtac
    end
  end.

Ltac rewrite_hyp :=
  match goal with
  | [H : ?x = _ |- context[?x]] =>
    rewrite H
  | [Ha : ?x = _, Hb : context[?x] |- _] =>
    rewrite Ha in Hb
  end.

Ltac eqb_auto :=
  match goal with
  | [H : ?n < ?m |- _] =>
    notHyp (n <> m);
    assert (n <> m);
    [crush|]
  | [H : ?n > ?m |- _] =>
    notHyp (n <> m);
    assert (n <> m);
    [crush|]
  | [H : ?n <> ?m |- _] =>
    notHyp (n =? m = false);
    let H' := fresh in
    assert (H' : n =? m = false);
    [apply <- Nat.eqb_neq; auto|]
      
  | [H : ?n <= ?m |- _] =>
    notHyp (n <=? m = true);
    let H' := fresh in
    assert (H' : n <=? m = true);
    [apply leb_correct; auto|]

  | [|- context[?n =? ?n]] =>
    rewrite Nat.eqb_refl
  | [H : context[?n =? ?n] |- _] =>
    rewrite Nat.eqb_refl in H

  | [Hneq : ?n =? ?m = false |- context[?n =? ?m]] =>
    rewrite Hneq
  | [Hneq : ?n =? ?m = false,
            H : context[?n =? ?n] |- _] =>
    rewrite Hneq in H

  | [Hge : ?n <=? ?m = true |- context[?n <=? ?m]] =>
    rewrite Hge
  | [Hge : ?n <=? ?m = true,
           H : context[?n <=? ?n] |- _] =>
    rewrite Hge in H
  end.

Ltac and_destruct :=
  repeat match goal with
         | [H : _ /\ _ |- _] =>
           destruct H
         end.

Ltac eq_auto n m :=
  destruct (Nat.eq_dec n m);
  subst;
  repeat eqb_auto.

(**
Definitions
 *)

Inductive var : Type :=
| hole : nat  -> var
| bnd : nat -> var.

Notation "'♢' n" := (hole n)(at level 40).
Notation "'α' n" := (bnd n)(at level 40).

Inductive label :=
| restricted : nat -> label
| unrestricted : nat -> label.

Inductive ty :Type :=
| top : ty
| bot : ty
| sel : var -> label -> ty
| decl : label -> ty -> ty -> ty
| all : ty -> ty -> ty.

Notation "'⊤'" := (top)(at level 40).
Notation "'⊥'" := (bot)(at level 40).
Notation "x '∘' l" := (sel x l)(at level 40).
Notation "⦃ l '⦂' τ1 '…' τ2 ⦄" := (decl l τ1 τ2)(at level 40).
Notation "'∀' τ1 '∙' τ2" := (all τ1 τ2)(at level 40).

Fixpoint max_n (τ : ty) : nat :=
  match τ with
  | α n ∘ l => n
  | ⦃ l ⦂ τ1 … τ2 ⦄ => max (max_n τ1) (max_n τ2)
  | (∀ τ1 ∙ τ2) => max (max_n τ1) (max_n τ2)
  | _ => 0
  end.

Notation "'ℳ' '[' τ ']'" := (max_n τ).

Inductive indexed {A : Type}{size : A -> nat}{n : nat} : Type :=
| index : forall a, size a <= n -> indexed.

Definition indexed_ty := @indexed ty max_n.

Definition index_ty {n : nat} := @index ty max_n n.

Notation "'⟦' τ '⊨' P '⟧'" := (index_ty τ P)(at level 40).

Inductive indexed_list {A : Type}{size : A -> nat} : nat -> Type :=
| id_empty : indexed_list 0
| id_update : forall n, @indexed A size n -> indexed_list n -> indexed_list (S n).

Definition S_ {A : Type}{size : A -> nat}{n : nat}(ι : @indexed A size n) : @indexed A size (S n) :=
  match ι with
  | index a P => index a (le_S (size a) n P)
  end.

Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
  {
  ret : forall {t : Type@{d}}, t -> m t;
  bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
  }.

Instance optionMonad : Monad option :=
  {
  ret T x :=
    Some x ;
  bind :=
    fun T U m f =>
      match m with
      | None => None
      | Some x => f x
      end

  }.

Fixpoint get {A : Type}{size : A -> nat}{m : nat}(Γ : @indexed_list A size m)(n : nat)
  : option (@indexed A size m) :=
  match Γ with
  | id_empty => None
  | id_update m' a Γ' =>
    if (m' =? (S n))
    then Some (S_ (a))
    else bind (get Γ' n) (fun ι => Some (S_ ι))
  end.

Notation "'[' n '⩽' a ']' '∈' Γ" := (get Γ n = Some a)(at level 40).

Lemma get_lt :
  forall {A : Type}{size : A -> nat}{m : nat}(Γ : indexed_list m) n (a : @indexed A size m),
    [ n ⩽ a ] ∈ Γ ->
    n < m.
Proof.
  intros A size m Γ;
    induction Γ;
    intros;
    simpl in *;
    [crush|].

  - destruct (Nat.eq_dec n (S n0));
      subst;
      auto.
    eqb_auto.
    rewrite H0 in H.
    specialize (IHΓ n0).
    destruct (get Γ n0);
      [|crush].
    specialize (IHΓ i0).
    crush.
Qed.

Definition env := @indexed_list ty max_n.

Definition empty := @id_empty ty max_n.

Definition update := @id_update ty max_n.

Notation "Γ ',' '[' n '⩽' τ ']'":= (update n τ Γ)(at level 40).

Fixpoint all_measure (τ : ty) : nat :=
  match τ with
  | (∀ τ1 ∙ τ2) => 1 + (all_measure τ1) + (all_measure τ2)
  | ⦃ l ⦂ τ1 … τ2 ⦄ => (all_measure τ1) + (all_measure τ2)
  | _ => 0
  end.

Notation "'𝒜' '[' τ ']'" := (all_measure τ)(at level 40).

Lemma ℳ_top :
  forall {n : nat}, ℳ [ ⊤ ] <= n.
Proof.
  intros;
    simpl;
    crush.
Qed.

Lemma ℳ_bot :
  forall {n : nat}, ℳ [ ⊥ ] <= n.
Proof.
  intros;
    simpl;
    crush.
Qed.

Lemma get_le :
  forall {A : Type}{size : A -> nat}{m : nat}{Γ : indexed_list m}{n : nat}{a : @indexed A size m},
    [ n ⩽ a ] ∈ Γ ->
    forall l, ℳ [α n ∘ l] <= m.
Proof.
  intros.
  simpl.
  eapply Nat.lt_le_incl, get_lt;
    eauto.
Qed.

Lemma ℳ_lower :
  forall {n : nat}{l : label}{τ1 τ2 : ty},
    ℳ [⦃ l ⦂ τ1 … τ2 ⦄] <= n ->
    ℳ [τ1] <= n.
Proof.
  intros.
  simpl in *.
  match goal with
  | [H : max ?a ?b <= ?n |- _] =>
    let H' := fresh in
    assert (H' : a <= max a b);
      [crush|crush]
  end.
Qed.

Lemma ℳ_upper :
  forall {n : nat}{l : label}{τ1 τ2 : ty},
    ℳ [⦃ l ⦂ τ1 … τ2 ⦄] <= n ->
    ℳ [τ2] <= n.
Proof.
  intros.
  simpl in *.
  match goal with
  | [H : max ?a ?b <= ?n |- _] =>
    let H' := fresh in
    assert (H' : b <= max a b);
      [crush|crush]
  end.
Qed.

Fixpoint sbst (n m : nat)(τ : ty) : ty :=
  match τ with
  | ♢ n' ∘ l => if n' =? n
               then (α m) ∘ l
               else τ
  | (∀ τ1 ∙ τ2) => (∀ (sbst n m τ1) ∙ (sbst (S n) m τ2))
  | ⦃ l ⦂ τ1 … τ2 ⦄ => ⦃ l ⦂ (sbst n m τ1) … (sbst n m τ2) ⦄
  | _ => τ
  end.

Notation "'[' n '↦' m ']' τ":=(sbst n m τ)(at level 40).

Lemma ℳ_sbst :
  forall {τ : ty}{n : nat}, ℳ [τ] <= n ->
                     forall {x : nat}, ℳ [[x ↦ n]τ] <= S n.
Proof.
  intro τ;
    induction τ;
    intros;
    simpl in *;
    eauto.

  - destruct v; auto.
    destruct (n0 =? x);
      auto.

  - match goal with
    | [Hmax : max ?n ?m <= ?x |- _] =>
      assert (n <= max n m);
        [crush|];
        assert (m <= max n m);
        [crush|];
        assert (n <= x);
        [crush|];
        assert (m <= x);
        [crush|]
    end;
      match goal with
      | [ |- context[max ?n ?m]] =>
        let H := fresh in
        destruct (Nat.max_dec n m) as [H|H];
          rewrite H
      end;
      try (rewrite IHτ1; auto);
      try (rewrite IHτ2; auto).

  - match goal with
    | [Hmax : max ?n ?m <= ?x |- _] =>
      assert (n <= max n m);
        [crush|];
        assert (m <= max n m);
        [crush|];
        assert (n <= x);
        [crush|];
        assert (m <= x);
        [crush|]
    end;
      match goal with
      | [ |- context[max ?n ?m]] =>
        let H := fresh in
        destruct (Nat.max_dec n m) as [H|H];
          rewrite H
      end;
      try (rewrite IHτ1; auto);
      try (rewrite IHτ2; auto).
Qed.

Lemma ℳ_defn :
  forall {n : nat}{l : label}{τ1 τ2 : ty},
    ℳ [τ1] <= n ->
    ℳ [τ2] <= n ->
    ℳ [⦃ l ⦂ τ1 … τ2 ⦄] <= n.
Proof.
  intros.
  simpl.
  match goal with
  | [Ha : ?a <= ?n,
          Hb : ?b <= ?n |- max ?a ?b <= ?n ] =>
    destruct (Nat.max_dec a b);
      crush
  end.
Qed.

Reserved Notation "Γ '⊢' τ1 '⩽' τ2"(at level 40).

Inductive sub {n : nat}: env n -> indexed_ty n -> indexed_ty n -> Prop :=
| s_top : forall Γ ι,
    Γ ⊢ ι ⩽ (⟦ ⊤ ⊨ ℳ_top⟧)

| s_bot : forall Γ ι,
    Γ ⊢ ι ⩽ (⟦ ⊥ ⊨ ℳ_bot ⟧)

| s_rfl : forall Γ m l (P : ℳ [α m ∘ l] <= n),
    Γ ⊢ ⟦ α m ∘ l ⊨ P ⟧ ⩽ ⟦ α m ∘ l ⊨ P ⟧

| s_upper : forall Γ m l τ1 τ2 ι
              (P : ℳ [⦃ l ⦂ τ1 … τ2 ⦄] <= n)
              (P' : [m ⩽ ⟦⦃ l ⦂ τ1 … τ2 ⦄ ⊨ P ⟧] ∈ Γ),
    Γ ⊢ ⟦ τ2 ⊨ ℳ_upper P ⟧ ⩽ ι ->
    Γ ⊢ ⟦ (α m ∘ l) ⊨ get_le P' l ⟧ ⩽ ι

| s_lower : forall Γ m l τ1 τ2 ι
              (P : ℳ [⦃ l ⦂ τ1 … τ2 ⦄] <= n)
              (P' : [m ⩽ ⟦⦃ l ⦂ τ1 … τ2 ⦄ ⊨ P ⟧] ∈ Γ),
    Γ ⊢ ι ⩽ (⟦ τ1 ⊨ ℳ_lower P ⟧) ->
    Γ ⊢ ι ⩽ ⟦ (α m ∘ l) ⊨ get_le P' l ⟧

| s_bnd : forall Γ l τ1 τ1' τ2 τ2'
            (P1 : ℳ [τ1] <= n)(P1' : ℳ [τ1'] <= n)
            (P2 : ℳ [τ2] <= n)(P2' : ℳ [τ2'] <= n),
    Γ ⊢ ⟦ τ1' ⊨ P1' ⟧ ⩽ (⟦ τ1 ⊨ P1 ⟧) ->
    Γ ⊢ ⟦ τ2 ⊨ P2 ⟧ ⩽ (⟦ τ2' ⊨ P2' ⟧) ->
    Γ ⊢ ⟦ ⦃ l ⦂ τ1 … τ2 ⦄ ⊨ ℳ_defn P1 P2 ⟧ ⩽ (⟦ ⦃ l ⦂ τ1' … τ2' ⦄ ⊨ ℳ_defn P1' P2' ⟧)

| s_all : forall (Γ : env n) (τ1 τ2 τ1' τ2' : ty)
            (P1 : ℳ [ τ1] <= n)(P2 : ℳ [τ2] <= n)
            (P1' : ℳ [ τ1'] <= n)(P2' : ℳ [τ2'] <= n)
            ι1 ι2 (ι1' ι2' : indexed_ty (S n)),
    Γ ⊢ (⟦ τ2 ⊨ P2 ⟧) ⩽ (⟦ τ1 ⊨ P1 ⟧) ->
    @sub (S n) (Γ , [n ⩽ (⟦ τ2 ⊨ P2 ⟧) ]) (⟦[0 ↦ n] τ1'⊨ ℳ_sbst P1'⟧) (⟦[0 ↦ n] τ2'⊨ ℳ_sbst P2'⟧) ->
    Γ ⊢ ι1 ⩽ ι2

where "Γ '⊢' τ1 '⩽' τ2" := (sub Γ τ1 τ2).
