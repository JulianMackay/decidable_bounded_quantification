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
            H : context[?n =? ?m] |- _] =>
    rewrite Hneq in H

  | [Hge : ?n <=? ?m = true |- context[?n <=? ?m]] =>
    rewrite Hge
  | [Hge : ?n <=? ?m = true,
           H : context[?n <=? ?n] |- _] =>
    rewrite Hge in H

  | [|- context[(?n1 =? ?n2) = (?n2 =? ?n1)]] =>
    rewrite Nat.eqb_sym
  | [H : context[(?n1 =? ?n2) = (?n2 =? ?n1)] |- _] =>
    rewrite Nat.eqb_sym in H

  | [H : ?n1 =? ?n2 = true |- _] =>
    let H' := fresh in
    assert (H' : n1 = n2);
    [apply Nat.eqb_eq in H; auto|subst; clear H]

  (*reflexivity*)
  | [H : context[?n =? ?n] |- _] =>
    rewrite Nat.eqb_refl in H
  | [|- context[?n =? ?n]] =>
    rewrite Nat.eqb_refl
  end.


Class Eq (A : Type) :=
  {eqb : A -> A -> bool;
   eqb_refl : forall a, eqb a a = true;
   eqb_sym : forall a1 a2, eqb a1 a2 = eqb a2 a1;
   eqb_eqp : forall a1 a2, eqb a1 a2 = true ->
                      a1 = a2;
   eqb_neq : forall a1 a2, eqb a1 a2 = false ->
                      a1 <> a2;
   neq_eqb : forall a1 a2, a1 <> a2 ->
                      eqb a1 a2 = false;
   eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}}.

Hint Resolve eqb_refl eqb_sym eqb_eqp eqb_neq neq_eqb eq_dec : eq_db.

Program Instance nat_Eq : Eq nat :=
  {eqb n m := (n =? m);
   eqb_refl := Nat.eqb_refl;
   eqb_sym := Nat.eqb_sym;
   eq_dec := Nat.eq_dec}.
Next Obligation.
  auto using beq_nat_eq.
Defined.
Next Obligation.
  apply Nat.eqb_neq; auto.
Defined.
Next Obligation.
  apply Nat.eqb_neq; auto.
Defined.

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

Inductive ρ_name :=
| ρ_n : nat -> ρ_name.

Inductive υ_name :=
| υ_n : nat -> υ_name.

Inductive name : Type :=
| ρ_ : nat -> name
| υ_ : nat -> name.

Ltac name_eq_auto :=
  match goal with
  | [a : name |- _] =>
    destruct a
  end.

Program Instance name_eq : Eq name :=
  { eqb x y := match x, y with
               | ρ_ n, ρ_ m => n =? m
               | υ_ n, υ_ m => n =? m
               | _, _ => false
               end
  }.
Next Obligation.
  split;
    intros;
    crush.
Defined.
Next Obligation.
  split;
    intros;
    crush.
Defined.
Next Obligation.
  name_eq_auto;
    eqb_auto;
    auto.
Defined.
Next Obligation.
  repeat name_eq_auto;
    auto;
    eqb_auto;
    auto.
Defined.
Next Obligation.
  repeat name_eq_auto;
    try eqb_auto;
    crush.
Defined.
Next Obligation.
  repeat name_eq_auto;
    repeat eqb_auto;
    crush;
    eqb_auto;
    crush.
Defined.
Next Obligation.
  repeat name_eq_auto;
    repeat eqb_auto;
    try solve [crush];
    match goal with
    | [n : nat, m : nat |- _] =>
      eq_auto n m
    end;
    crush.
Defined.
Next Obligation.
  repeat name_eq_auto;
    match goal with
    | [n : nat, m : nat |- _] =>
      eq_auto n m
    end;
    auto;
    try solve [right; crush].
Defined.

Inductive var : Type :=
| hole : nat -> var
| bnd : name -> var.

Inductive ty :Type :=
| top : ty
| t_var : var -> ty
| t_arr : ty -> ty -> ty
| all : ty -> ty -> ty.

Notation "'⊤'" := (top)(at level 40).
(*Notation "'ρ♢' n" := (t_var (hole (ρ_ n)))(at level 40).
Notation "'υ♢' n" := (t_var (hole (υ_ n)))(at level 40).*)
Notation "'ρ' n" := (t_var (bnd (ρ_ n)))(at level 40).
Notation "'υ' n" := (t_var (bnd (υ_ n)))(at level 40).
Notation "'♢' n" := (t_var (hole n))(at level 41).
Notation "'α' n" := (t_var (bnd n))(at level 41).
Notation "τ1 '⟶' τ2" := (t_arr τ1 τ2)(at level 40).
Notation "'∀' τ1 '∙' τ2" := (all τ1 τ2)(at level 40).

Fixpoint ℳ (τ : ty) : nat :=
  match τ with
  | ⊤ => 0
  | ρ n => n
  | υ n => n
  | (∀ τ1 ∙ τ2) => max (ℳ τ1) (ℳ τ2)
  | τ1 ⟶ τ2 => max (ℳ τ1) (ℳ τ2)
  | _ => 0
  end.

Definition ℳ_le (n : nat)(τ : ty) := ℳ τ <= n.

(*Notation "'ℳ' '[' τ ']'" := (max_ τ).*)

Ltac ty_constructors :=
  match goal with
  | [H : top = t_var _ |- _] =>
    inversion H
  | [H : top = all _ _ |- _] =>
    inversion H

  | [H : t_var _ = top |- _] =>
    inversion H
  | [H : t_var _ = all _ _ |- _] =>
    inversion H
  | [H : t_var _ = t_var _ |- _] =>
    symmetry in H;
    inversion H;
    subst;
    clear H

  | [H : all _ _ = top |- _] =>
    inversion H
  | [H : all _ = t_var _ |- _] =>
    inversion H
  | [H : all _ _ = all _ _ |- _] =>
    symmetry in H;
    inversion H;
    subst;
    clear H
  end.

Inductive restricted : ty -> Prop :=
| rest_top : restricted (⊤)
| rest_bnd : forall n, restricted (ρ n)
| rest_hole : forall n, restricted (♢ n)
| rest_arr : forall τ1 τ2, restricted τ1 ->
                      restricted τ2 ->
                      restricted (τ1 ⟶ τ2).

(*
lt_ty is unclear ...
do we need to include the lt_all and lt_var2 cases?
we only care about restricted types.
should we just merge lt_ty with restricted?
i.e. should restricted say something like: 
"restricted τ n holds if there is no bounded quantification in τ,
and n is an upper bound on the variables in τ"
 *)
Inductive lt_ty : ty -> nat -> Prop :=
| lt_top  : forall n, lt_ty (⊤) n
| lt_var1 : forall n m, n < m ->
                   lt_ty (ρ n) m
| lt_var2 : forall n m, n < m ->
                   lt_ty (υ n) m
| lt_arr  : forall τ1 τ2 n, lt_ty τ1 n ->
                       lt_ty τ2 n ->
                       lt_ty (τ1 ⟶ τ2) n
| lt_all  : forall τ1 τ2 n, lt_ty τ1 n ->
                       lt_ty τ2 n ->
                       lt_ty (∀ τ1 ∙ τ2) n.

(* 
restricted_ty is something like a dependent pair type, see HoTT in Coq 
restricted_ty packages up a type with a proof that it contains no 
bounded quantification, and also that all variables are bounded by n
 *)

Inductive indexed {A : Type}{f : A -> Prop} :=
| index : forall a, f a -> indexed.

Notation "'⟦' τ '⊨' P '⟧'" := (index τ P)(at level 40).

Definition unwrap {A : Type}{f : A -> Prop}(ι : @indexed A f) :=
  match ι with
  | index a _ => a
  end.
  
Definition restricted_ty := @indexed ty restricted.

Inductive lt_r : restricted_ty -> nat -> Prop :=
| lt_ρ : forall n τ (P : restricted τ),
    lt_ty τ n -> lt_r (⟦ τ ⊨ P ⟧) n.

Definition total_map (A B : Type)`{Eq A} := A -> B.

Definition t_emtpy {A B : Type}`{Eq A}(b : B) : total_map A B := fun _ => b.

Definition t_update {A B : Type}`{Eq A}(a : A)(b : B)(Γ : total_map A B) : total_map A B :=
  fun a' => if eqb a' a
        then b
        else Γ a'.

Definition partial_map (A B : Type)`{Eq A} := total_map A (option B).

Definition empty {A B : Type}`{Eq A} : partial_map A B := t_emtpy None.

Definition update {A B : Type}`{Eq A}(a : A)(b : B)(Γ : partial_map A B) : partial_map A B :=
  t_update a (Some b) Γ.

Definition ty_map := partial_map name ty.

Notation "'[' a '⩽' b ']' '∈' c" := (c a = Some b)(at level 40).

Definition separated (Γ : ty_map) :=
  forall n τ, [ ρ_ n  ⩽ τ ] ∈ Γ ->
         restricted τ.

Definition id x := match x with
                   | ρ_ n => n
                   | υ_ n => n
                   end.

Definition ord (Γ : ty_map) :=
  forall x τ, Γ x = Some τ ->
         ℳ τ < (id x).

Definition wf := (fun Γ => separated Γ /\ ord Γ).

Definition env := @indexed ty_map wf.

Lemma update_ord :
  forall {Γ : ty_map}{x : name}{τ : ty},
    ord Γ ->
    ℳ τ < id x ->
    ord (update x τ Γ).
Proof.
  intros.
  unfold ord, update, t_update;
    intros.
  - destruct (eq_dec x x0);
      subst.
    rewrite eqb_refl in H1.
    inversion H1; subst;
      auto.
    rewrite neq_eqb in H1; auto;
      intros Hcontra.
Qed.

Lemma update_sep_ρ :
  forall {Γ : ty_map}{n : name}{τ : ty},
    separated Γ ->
    restricted τ ->
    separated (update n τ Γ).
Proof.
  intros.
  unfold separated, update, t_update in *;
    intros.
  destruct (eq_dec (ρ_ n0) n);
    subst.
  - rewrite eqb_refl in H1.
    inversion H1;
      subst;
      auto.
  - rewrite neq_eqb in H1;
      auto.
    eapply H; eauto.
Qed.

Lemma update_sep_υ :
  forall {Γ : ty_map}{n : nat}{τ : ty},
    separated Γ ->
    separated (update (υ_ n) τ Γ).
Proof.
  intros.
  unfold separated, update, t_update in *;
    intros.
  rewrite neq_eqb in H0.
  - eapply H; eauto.
  - intros Hcontra;
      crush.
Qed.

Lemma update_ρ :
  forall {Γ : ty_map}{n : nat}{τ : ty},
    wf Γ ->
    restricted τ /\ ℳ τ < n ->
    wf (update (ρ_ n) τ Γ).
Proof.
  intros;
    unfold wf in *;
    and_destruct.
  split.
  - apply update_sep_ρ;
      auto.
  - apply update_ord;
      auto.
Qed.

Lemma update_υ :
  forall {Γ : ty_map}{n : nat}{τ : ty},
    wf Γ ->
    ℳ τ < n ->
    wf (update (υ_ n) τ Γ).
Proof.
  intros;
    unfold wf in *;
    and_destruct.
  split.
  - apply update_sep_υ;
      auto.
  - apply update_ord;
      auto.
Qed.

Definition ρ_update (n : nat)(τ : ty)(P : restricted τ /\ ℳ τ < n)(Γ : env) :=
  match Γ with
  | index β P' => index (update (ρ_ n) τ β) (update_ρ P' P)
  end.

Definition υ_update (n : nat)(τ : ty)(P : ℳ τ < n)(Γ : env) :=
  match Γ with
  | index β P' => index (update (υ_ n) τ β)(update_υ P' P)
  end.

Notation "Γ ',' '[' P '⫤ρ' n '⩽' τ ']'":=(update n τ P Γ)(at level 40).
Notation "Γ ',' '[' P '⫤υ' n '⩽' τ ']'":=(υ_update n τ P Γ)(at level 40).

Definition map_size {A : Type}(Γ : nat -> option A)(n : nat) :=
  (forall m a, m <= n <->
          Γ m = Some a).

Fixpoint sbst (m : nat)(n : name)(τ : ty) : ty :=
  match τ with
  | ♢ n' => if n' =? m
           then (α n)
           else τ
  | (∀ τ1 ∙ τ2) => (∀ (sbst m n τ1) ∙ (sbst (S m) n τ2))
  | τ1 ⟶ τ2 => (sbst m n τ1) ⟶ (sbst m n τ2)
  | _ => τ
  end.

Notation "'[' m '↦' n ']' τ":=(sbst m n τ)(at level 40).

(*Fixpoint all_measure (τ : ty) :=
  match τ with
  | (∀ τ1 ∙ τ2) => 1 + (all_measure τ1) + (all_measure τ2)
  | _ => 0
  end.

Notation "'𝒜' '[' τ ']'" := (all_measure τ)(at level 40).*)



Inductive closed : ty -> nat -> Prop :=
| cl_rbnd : forall n m, closed (ρ m) n
| cl_ubnd : forall n m, closed (υ m) n
| cl_rhole : forall n m, m < n ->
                    closed (♢ m) n
| cl_top : forall n, closed (⊤) n
| cl_arr : forall n τ1 τ2, closed τ1 n ->
                      closed τ2 n ->
                      closed (τ1 ⟶ τ2) n
| cl_all : forall n τ1 τ2, closed τ1 n ->
                      closed τ2 (S n) ->
                      closed (∀ τ1 ∙ τ2) n.

Hint Constructors closed : f_sub_db.

Lemma max_n_lt_all_1 :
  forall τ1 τ2 n, ℳ (∀ τ1 ∙ τ2) < n ->
             ℳ τ1 < n.
Proof.
  intros;
    simpl in *.
  assert (ℳ τ1 <= max (ℳ τ1) (ℳ τ2));
    [crush|crush].
Qed.

Lemma ℳ_top :
  forall {n : nat}, ℳ (⊤) <= n.
Proof.
  intros;
    simpl;
    crush.
Qed.
  

(*Lemma ℳ_sbst :
  forall {τ : ty}{n : nat}, ℳ [τ] <= n ->
                     forall {x : nat}, ℳ [[x ↦ n]τ] <= S n.
Proof.
  intro τ;
    induction τ;
    intros;
    simpl in *;
    eauto.

  - destruct v; auto.
    destruct n0;
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
Qed.*)

(*Fixpoint weight (Γ : env)(τ : ty) :=
  match τ with
  | ρ n => 0
  | υ n => match get n Γ with
          | Some (_, m) => m
          | None => 0
          end
  | τ1 ⟶ τ2 => max (weight Γ τ1) (weight Γ τ2)
  | (∀ τ1 ∙ τ2) => max (weight Γ τ1) (weight ((τ1, weight Γ τ1) :: Γ) τ2)
  | _ => 0
  end.*)

(*Lemma ℳ_all :
  forall {τ : ty}{n : nat}, ℳ [τ] <= n ->
                     forall {x : nat}, ℳ [[x ↦ n]τ] <= S n.
Proof.
Qed.*)

(*Definition bounded (Γ : env)(n : nat) :=
  forall m τ, ([ ρ_ m ⩽ τ] ∈ Γ ->
          m <= n) /\
         ([ υ_ m ⩽ τ] ∈ Γ ->
          m <= n).*)

(*Inductive indexed {A : Type}{size : A -> nat -> Prop}{n : nat} : Type :=
| index : forall a, size a n -> indexed.*)

Definition indexed_ty (n : nat) := @indexed ty (ℳ_le n).

(*Notation "'⌈' a ⦂ P '⌉'" := (@index ty (ℳ_le n) a P)(at level 40).*)

(*Definition indexed_env (n : nat) := @indexed env bounded n.*)

(*Lemma bnd_impl1 :
  forall {Γ : env}{n : nat}{m : name}{τ : ty},
      [m ⩽ τ] ∈ Γ ->
      ℳ_le n (α m) ->
      ℳ_le n τ.
Proof.
  intros.
Admitted.*)

Lemma ℳ_le_arr1 :
  forall {τ1 τ2 : ty}{n : nat},
    ℳ_le n (τ1 ⟶ τ2) ->
    ℳ_le n τ1.
Proof.
  intros.
  unfold ℳ_le in *;
    simpl in *.
  match goal with
  | [ H : max ?n1 ?n2 <= ?m |- ?n1 <= ?m] =>
    let H' := fresh in
    assert (H' : n1 <= max n1 n2);
      [crush|crush]
  end.
Qed.

Lemma ℳ_le_arr2 :
  forall {τ1 τ2 : ty}{n : nat},
    ℳ_le n (τ1 ⟶ τ2) ->
    ℳ_le n τ2.
Proof.
  intros.
  unfold ℳ_le in *;
    simpl in *.
  match goal with
  | [ H : max ?n1 ?n2 <= ?m |- ?n2 <= ?m] =>
    let H' := fresh in
    assert (H' : n2 <= max n1 n2);
      [crush|crush]
  end.
Qed.

Lemma ℳ_le_all1 :
  forall {τ1 τ2 : ty}{n : nat},
    ℳ_le n (∀ τ1 ∙ τ2) ->
    ℳ_le n τ1.
Proof.
  intros.
  unfold ℳ_le in *.
  simpl in *.
  match goal with
  | [ H : max ?n1 ?n2 <= ?m |- ?n1 <= ?m] =>
    let H' := fresh in
    assert (H' : n1 <= max n1 n2);
      [crush|crush]
  end.
Qed.

Lemma ℳ_le_all2 :
  forall {τ1 τ2 : ty}{n : nat},
    ℳ_le n (∀ τ1 ∙ τ2) ->
    ℳ_le n τ2.
Proof.
  intros.
  unfold ℳ_le in *.
  simpl in *.
  match goal with
  | [ H : max ?n1 ?n2 <= ?m |- ?n2 <= ?m] =>
    let H' := fresh in
    assert (H' : n2 <= max n1 n2);
      [crush|crush]
  end.
Qed.

Lemma ℳ_lt_arr1 :
  forall {τ1 τ2 : ty}{n : nat},
    ℳ (τ1 ⟶ τ2) < n ->
    ℳ τ1 < n.
Proof.
  intros;
    simpl in *.
  match goal with
  | [ H : max ?n1 ?n2 < ?m |- ?n1 < ?m] =>
    let H' := fresh in
    assert (H' : n1 <= max n1 n2);
      [crush|crush]
  end.
Qed.

Lemma ℳ_lt_arr2 :
  forall {τ1 τ2 : ty}{n : nat},
    ℳ (τ1 ⟶ τ2) < n ->
    ℳ τ2 < n.
Proof.
  intros;
    simpl in *.
  match goal with
  | [ H : max ?n1 ?n2 < ?m |- ?n2 < ?m] =>
    let H' := fresh in
    assert (H' : n2 <= max n1 n2);
      [crush|crush]
  end.
Qed.

Lemma ℳ_lt_all1 :
  forall {τ1 τ2 : ty}{n : nat},
    ℳ (∀ τ1 ∙ τ2) < n ->
    ℳ τ1 < n.
Proof.
  intros;
    simpl in *.
  match goal with
  | [ H : max ?n1 ?n2 < ?m |- ?n1 < ?m] =>
    let H' := fresh in
    assert (H' : n1 <= max n1 n2);
      [crush|crush]
  end.
Qed.

Lemma ℳ_lt_all2 :
  forall {τ1 τ2 : ty}{n : nat},
    ℳ (∀ τ1 ∙ τ2) < n ->
    ℳ τ2 < n.
Proof.
  intros;
    simpl in *.
  match goal with
  | [ H : max ?n1 ?n2 < ?m |- ?n2 < ?m] =>
    let H' := fresh in
    assert (H' : n2 <= max n1 n2);
      [crush|crush]
  end.
Qed.

Lemma ℳ_le_sbst_ρ :
  forall {τ : ty}{n m : nat},
    ℳ_le m τ ->
    ℳ_le (S m) ([n ↦ ρ_ (S m)] τ).
Proof.
  intro τ;
    induction τ;
    intros;
    eauto;
    unfold ℳ_le in *;
    simpl in *;
    eauto.

  - destruct v;
      auto.
    destruct (n0 =? n);
      auto.

  -  match goal with
     | [ H : max ?n1 ?n2 <= ?m |- _] =>
       let Ha := fresh in
       let Hb := fresh in
       assert (Ha : n1 <= max n1 n2);
         [crush|];
         assert (Hb : n2 <= max n1 n2);
           [crush|]
     end.
     repeat match goal with
            | [Ha : ?n1 <= ?n2,
                    Hb : ?n2 <= ?n3 |- _] =>
              notHyp (n1 <= n3);
                let H' := fresh in
                assert (H' : n1 <= n3);
                  [crush|]
            end.
     specialize (IHτ1 n m H3).
     specialize (IHτ2 n m H2).
     match goal with
     | [|- max ?n ?m <= _] =>
       let H := fresh in
       destruct (Max.max_dec n m) as [H|H];
         rewrite H
     end;
       auto.

  - match goal with
     | [ H : max ?n1 ?n2 <= ?m |- _] =>
       let Ha := fresh in
       let Hb := fresh in
       assert (Ha : n1 <= max n1 n2);
         [crush|];
         assert (Hb : n2 <= max n1 n2);
           [crush|]
     end.
     repeat match goal with
            | [Ha : ?n1 <= ?n2,
                    Hb : ?n2 <= ?n3 |- _] =>
              notHyp (n1 <= n3);
                let H' := fresh in
                assert (H' : n1 <= n3);
                  [crush|]
            end.
     specialize (IHτ1 n m H3).
     specialize (IHτ2 (S n) m H2).
     match goal with
     | [|- max ?n ?m <= _] =>
       let H := fresh in
       destruct (Max.max_dec n m) as [H|H];
         rewrite H
     end;
       auto.
    
Qed.

Lemma ℳ_le_sbst_υ :
  forall {τ : ty}{n m : nat},
    ℳ_le m τ ->
    ℳ_le (S m) ([n ↦ υ_ (S m)] τ).
Proof.
  intro τ;
    induction τ;
    intros;
    eauto;
    unfold ℳ_le in *;
    simpl in *;
    eauto.

  - destruct v;
      auto.
    destruct (n0 =? n);
      auto.

  -  match goal with
     | [ H : max ?n1 ?n2 <= ?m |- _] =>
       let Ha := fresh in
       let Hb := fresh in
       assert (Ha : n1 <= max n1 n2);
         [crush|];
         assert (Hb : n2 <= max n1 n2);
           [crush|]
     end.
     repeat match goal with
            | [Ha : ?n1 <= ?n2,
                    Hb : ?n2 <= ?n3 |- _] =>
              notHyp (n1 <= n3);
                let H' := fresh in
                assert (H' : n1 <= n3);
                  [crush|]
            end.
     specialize (IHτ1 n m H3).
     specialize (IHτ2 n m H2).
     match goal with
     | [|- max ?n ?m <= _] =>
       let H := fresh in
       destruct (Max.max_dec n m) as [H|H];
         rewrite H
     end;
       auto.

  - match goal with
     | [ H : max ?n1 ?n2 <= ?m |- _] =>
       let Ha := fresh in
       let Hb := fresh in
       assert (Ha : n1 <= max n1 n2);
         [crush|];
         assert (Hb : n2 <= max n1 n2);
           [crush|]
     end.
     repeat match goal with
            | [Ha : ?n1 <= ?n2,
                    Hb : ?n2 <= ?n3 |- _] =>
              notHyp (n1 <= n3);
                let H' := fresh in
                assert (H' : n1 <= n3);
                  [crush|]
            end.
     specialize (IHτ1 n m H3).
     specialize (IHτ2 (S n) m H2).
     match goal with
     | [|- max ?n ?m <= _] =>
       let H := fresh in
       destruct (Max.max_dec n m) as [H|H];
         rewrite H
     end;
       auto.
    
Qed.

Lemma ℳ_lt_sbst_ρ :
  forall {τ : ty}{n m : nat},
    ℳ τ < m ->
    ℳ ([n ↦ ρ_ m] τ) < (S m).
Proof.
  intro τ;
    induction τ;
    intros;
    eauto;
    simpl in *;
    eauto.

  - destruct v;
      auto.
    destruct (n0 =? n);
      auto.

  -  match goal with
     | [ H : max ?n1 ?n2 < ?m |- _] =>
       let Ha := fresh in
       let Hb := fresh in
       assert (Ha : n1 <= max n1 n2);
         [crush|];
         assert (Hb : n2 <= max n1 n2);
           [crush|]
     end.
     repeat match goal with
            | [Ha : ?n1 <= ?n2,
                    Hb : ?n2 < ?n3 |- _] =>
              notHyp (n1 < n3);
                let H' := fresh in
                assert (H' : n1 < n3);
                  [crush|]
            end.
     specialize (IHτ1 n m H3).
     specialize (IHτ2 n m H2).
     match goal with
     | [|- max ?n ?m < _] =>
       let H := fresh in
       destruct (Max.max_dec n m) as [H|H];
         rewrite H
     end;
       auto.

  - match goal with
     | [ H : max ?n1 ?n2 < ?m |- _] =>
       let Ha := fresh in
       let Hb := fresh in
       assert (Ha : n1 <= max n1 n2);
         [crush|];
         assert (Hb : n2 <= max n1 n2);
           [crush|]
     end.
     repeat match goal with
            | [Ha : ?n1 <= ?n2,
                    Hb : ?n2 < ?n3 |- _] =>
              notHyp (n1 < n3);
                let H' := fresh in
                assert (H' : n1 < n3);
                  [crush|]
            end.
     specialize (IHτ1 n m H3).
     specialize (IHτ2 (S n) m H2).
     match goal with
     | [|- max ?n ?m < _] =>
       let H := fresh in
       destruct (Max.max_dec n m) as [H|H];
         rewrite H
     end;
       auto.
    
Qed.

Lemma ℳ_lt_sbst_υ :
  forall {τ : ty}{n m : nat},
    ℳ τ < m ->
    ℳ ([n ↦ υ_ m] τ) < (S m).
Proof.
  intro τ;
    induction τ;
    intros;
    eauto;
    simpl in *;
    eauto.

  - destruct v;
      auto.
    destruct (n0 =? n);
      auto.

  -  match goal with
     | [ H : max ?n1 ?n2 < ?m |- _] =>
       let Ha := fresh in
       let Hb := fresh in
       assert (Ha : n1 <= max n1 n2);
         [crush|];
         assert (Hb : n2 <= max n1 n2);
           [crush|]
     end.
     repeat match goal with
            | [Ha : ?n1 <= ?n2,
                    Hb : ?n2 < ?n3 |- _] =>
              notHyp (n1 < n3);
                let H' := fresh in
                assert (H' : n1 < n3);
                  [crush|]
            end.
     specialize (IHτ1 n m H3).
     specialize (IHτ2 n m H2).
     match goal with
     | [|- max ?n ?m < _] =>
       let H := fresh in
       destruct (Max.max_dec n m) as [H|H];
         rewrite H
     end;
       auto.

  - match goal with
     | [ H : max ?n1 ?n2 < ?m |- _] =>
       let Ha := fresh in
       let Hb := fresh in
       assert (Ha : n1 <= max n1 n2);
         [crush|];
         assert (Hb : n2 <= max n1 n2);
           [crush|]
     end.
     repeat match goal with
            | [Ha : ?n1 <= ?n2,
                    Hb : ?n2 < ?n3 |- _] =>
              notHyp (n1 < n3);
                let H' := fresh in
                assert (H' : n1 < n3);
                  [crush|]
            end.
     specialize (IHτ1 n m H3).
     specialize (IHτ2 (S n) m H2).
     match goal with
     | [|- max ?n ?m < _] =>
       let H := fresh in
       destruct (Max.max_dec n m) as [H|H];
         rewrite H
     end;
       auto.
    
Qed.

Lemma ℳ_le_lt :
  forall {τ : ty}{n : nat},
    ℳ_le n τ ->
    ℳ τ < S n.
Proof.
  intros;
    unfold ℳ_le in *.
  crush.
Qed.

Reserved Notation "Γ '⊢' τ1 '⩽' τ2"(at level 40).

(**
I don't think I need to index the context if the types are indexed.
i.e. we already have that for any [n ⩽ τ] ∈ Γ, for any m in τ, m < n.
 *)

Inductive sub {n : nat} : env -> @indexed_ty n -> @indexed_ty n -> Prop :=
| s_top : forall Γ τ, Γ ⊢ τ ⩽ (⟦ (⊤) ⊨  ℳ_top⟧)

(**
(P : ℳ (α m) <= n)
*)
| s_rfl : forall Γ m P, Γ ⊢ ⟦ α m ⊨  P ⟧ ⩽ ⟦ (α m) ⊨ P ⟧

where "Γ '⊢' ι1 '⩽' ι2" := (sub Γ ι1 ι2).

(**
(P' : ℳ_le (α m) n)
*)
| s_var : forall Γ m τ1 ι (P : [ m ⩽ τ1 ] ∈ Γ) P',
    Γ ⊢ ⟦ τ1 ⊨ bnd_impl1 P P' ⟧ ⩽ ι ->
    Γ ⊢ ⟦ α m ⊨ P' ⟧ ⩽ ι

(**
(P1 : ℳ_le (τ1 ⟶ τ1') n)
(P2 : ℳ_le (τ2 ⟶ τ2') n)
*)
| s_arr : forall Γ τ1 τ2 τ1' τ2' P1 P2,
    Γ ⊢ ⟦ τ2 ⊨ ℳ_le_arr1 P2 ⟧ ⩽ (⟦ τ1 ⊨ ℳ_le_arr1 P1 ⟧) ->
    Γ ⊢ ⟦ τ1' ⊨ ℳ_le_arr2 P1 ⟧ ⩽ (⟦ τ2' ⊨ ℳ_le_arr2 P2 ⟧) ->
    Γ ⊢ ⟦ (τ1 ⟶ τ1') ⊨ P1 ⟧ ⩽ ⟦ (τ2 ⟶ τ2') ⊨ P2 ⟧

(**
(ρP: restricted τ)
(P1 : ℳ_le (∀ τ ∙ τ1) n)
(P2 : ℳ_le (∀ τ ∙ τ2) n)
*)
| s_all : forall Γ τ τ1 τ2 P1 P2,
    @sub (S n)
         (Γ, [ℳ_le_lt (ℳ_le_all1 P1) ⫤υ S n ⩽ τ])
         (⟦ [0 ↦ υ_ (S n)] τ1 ⊨ ℳ_le_sbst_υ (ℳ_le_all2 P1)⟧)
         (⟦ [0 ↦ υ_ (S n)] τ2 ⊨ ℳ_le_sbst_υ (ℳ_le_all2 P2)⟧) ->
    Γ ⊢ ⟦(∀ τ ∙ τ1) ⊨ P1⟧ ⩽ ⟦ (∀ τ ∙ τ2) ⊨ P2⟧
(**
(P1 : ℳ_le (∀ τ1 ∙ τ1') n)
(P2 : ℳ_le (∀ τ2 ∙ τ2') n)
*)
| s_all_kernel : forall Γ τ1 τ1' τ2 τ2' (ρP : restricted τ2) P1 P2,
(*                   (P1 : ℳ_le (∀ τ1 ∙ τ1') n)
                   (P2 : ℳ_le (∀ τ2 ∙ τ2') n),*)
    Γ ⊢ (⟦ τ2 ⊨ ℳ_le_all1 P2 ⟧) ⩽ (⟦ τ1 ⊨ ℳ_le_all1 P1 ⟧) ->
    @sub (S n)
         (Γ, [ℳ_le_lt (ℳ_le_all1 P2) ⫤ρ S n ⩽ ⟦ τ2 ⊨ ρP ⟧])
         (⟦ [0 ↦ ρ_ (S n)] τ1' ⊨ ℳ_le_sbst_ρ (ℳ_le_all2 P1)⟧)
         (⟦ [0 ↦ ρ_ (S n)] τ2' ⊨ ℳ_le_sbst_ρ (ℳ_le_all2 P2)⟧) ->
    Γ ⊢ (⟦ (∀ τ1 ∙ τ1') ⊨ P1⟧) ⩽ (⟦(∀ τ2 ∙ τ2') ⊨ P2⟧)

where "Γ '⊢' ι1 '⩽' ι2" := (sub Γ ι1 ι2).

(**
𝒟 : syntactic depth function
*)

Fixpoint 𝒟 (τ : ty) :=
  match τ with
  | (∀ τ1 ∙ τ2) => 1 + (𝒟 τ1) + (𝒟 τ2)
  | τ1 ⟶ τ2 => 1 + (𝒟 τ1) + (𝒟 τ2)
  | _ => 1
  end.

Require Import Coq.Program.Wf.

(**
𝒜 : quantification depth function
 *)

Lemma lt_Sn :
  forall n m, n < m ->
         n < S m.
  crush.
Qed.

Ltac 𝒜_solve :=
  simpl in *;
  match goal with
  | [|- 𝒟 ?τ1 < S (𝒟 ?τ1 + 𝒟 ?τ2) ] =>
    rewrite plus_n_Sm, <- plus_Snm_nSm;
    apply lt_plus_trans
  | [|- 𝒟 ?τ2 < S (𝒟 ?τ1 + 𝒟 ?τ2) ] =>
    rewrite plus_n_Sm, plus_comm;
    apply lt_plus_trans
  | [|- _ /\ _] =>
    split;
    intros;
    intros Hcontra;
    crush
  end;
  auto.

(**
[Solve Obligations with 𝒜_solve] does not work for some reason
*)
Program Fixpoint 𝒜 {n : nat}(Γ : env)(τ : ty)(P : ℳ τ < n)
        {measure (𝒟 τ)} :=
  match τ with
  | τ1 ⟶ τ2 =>  max (𝒜 Γ τ1 (@ℳ_lt_arr1 τ1 τ2 n P))
                   (𝒜 Γ τ2 (@ℳ_lt_arr2 τ1 τ2 n P))
  | (∀ τ1 ∙ τ2) => 1 +
                  (𝒜 Γ τ1 (@ℳ_lt_all1 τ1 τ2 n P)) +
                  (𝒜 (Γ, [P ⫤υ n ⩽ τ]) τ2 (@ℳ_lt_all2 τ1 τ2 n P))
  | _ => 0
  end.
(**Solve Obligations with 𝒜_solve.*)
Next Obligation.
  𝒜_solve.
Defined.
Next Obligation.
  𝒜_solve.
Defined.
Next Obligation.
  simpl in *.
  𝒜_solve.
Defined.
Next Obligation.
  𝒜_solve.
Defined.
Next Obligation.
  𝒜_solve.
Defined.
Next Obligation.
  𝒜_solve.
Defined.


