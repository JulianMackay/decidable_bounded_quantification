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

Inductive name :=
| restrict : nat -> name
| unrestrict : nat -> name.

Inductive var : Type :=
| hole : name -> var
| bnd : name -> var.

Inductive ty :Type :=
| top : ty
| t_var : var -> ty
| t_arr : ty -> ty -> ty
| all : ty -> ty -> ty.

Notation "'⊤'" := (top)(at level 40).
Notation "'ρ♢' n" := (t_var (hole (restrict n)))(at level 40).
Notation "'υ♢' n" := (t_var (hole (unrestrict n)))(at level 40).
Notation "'ρ̇' n" := (t_var (bnd (restrict n)))(at level 40).
Notation "'υ̇' n" := (t_var (bnd (unrestrict n)))(at level 40).
Notation "'♢' n" := (t_var (hole n))(at level 41).
Notation "'α̇' n" := (t_var (bnd n))(at level 41).
Notation "τ1 '⟶' τ2" := (t_arr τ1 τ2)(at level 40).
Notation "'∀' τ1 '∙' τ2" := (all τ1 τ2)(at level 40).

Fixpoint max_n (τ : ty) : nat :=
  match τ with
  | ⊤ => 0
  | ρ̇ n => n
  | υ̇ n => n
  | (∀ τ1 ∙ τ2) => max (max_n τ1) (max_n τ2)
  | τ1 ⟶ τ2 => max (max_n τ1) (max_n τ2)
  | _ => 0
  end.

Notation "'ℳ' '[' τ ']'" := (max_n τ).

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
  | _ => 0
  end.

Notation "'𝒜' '[' τ ']'" := (all_measure τ)(at level 40).

(*Definition all_measure_env {n : nat}(Γ : env n) :=
  //map all_measure Γ.*)

Lemma get_le_ρ :
  forall {A : Type}{size : A -> nat}{m : nat}{Γ : indexed_list m}{n : nat}{a : @indexed A size m},
    [ n ⩽ a ] ∈ Γ ->
    ℳ [ρ̇ n] <= m.
Proof.
  intros.
  simpl.
  eapply Nat.lt_le_incl, get_lt;
    eauto.
Qed.

Lemma get_le_υ :
  forall {A : Type}{size : A -> nat}{m : nat}{Γ : indexed_list m}{n : nat}{a : @indexed A size m},
    [ n ⩽ a ] ∈ Γ ->
    ℳ [υ̇ n] <= m.
Proof.
  intros.
  simpl.
  eapply Nat.lt_le_incl, get_lt;
    eauto.
Qed.

Fixpoint sbst (n m : nat)(τ : ty) : ty :=
  match τ with
  | ρ♢ n' => if n' =? n
           then (ρ̇ m)
           else τ
  | υ♢ n' => if n' =? n
           then (υ̇ m)
           else τ
  | (∀ τ1 ∙ τ2) => (∀ (sbst n m τ1) ∙ (sbst (S n) m τ2))
  | τ1 ⟶ τ2 => (sbst n m τ1) ⟶ (sbst n m τ2)
  | _ => τ
  end.

Notation "'[' n '↦' m ']' τ":=(sbst n m τ)(at level 40).

(*Fixpoint all_measure (τ : ty) :=
  match τ with
  | (∀ τ1 ∙ τ2) => 1 + (all_measure τ1) + (all_measure τ2)
  | _ => 0
  end.

Notation "'𝒜' '[' τ ']'" := (all_measure τ)(at level 40).*)



Inductive closed : ty -> nat -> Prop :=
| cl_rbnd : forall n m, closed (ρ̇ m) n
| cl_ubnd : forall n m, closed (υ̇ m) n
| cl_rhole : forall n m, m < n ->
                    closed (ρ♢ m) n
| cl_uhole : forall n m, m < n ->
                    closed (υ♢ m) n
| cl_top : forall n, closed (⊤) n
| cl_arr : forall n τ1 τ2, closed τ1 n ->
                      closed τ2 n ->
                      closed (τ1 ⟶ τ2) n
| cl_all : forall n τ1 τ2, closed τ1 n ->
                      closed τ2 (S n) ->
                      closed (∀ τ1 ∙ τ2) n.

Hint Constructors closed : f_sub_db.

Lemma max_n_lt_all_1 :
  forall τ1 τ2 n, ℳ [∀ τ1 ∙ τ2] < n ->
             ℳ [τ1] < n.
Proof.
  intros;
    simpl in *.
  assert (ℳ [τ1] <= max ℳ [τ1] ℳ [τ2]);
    [crush|crush].
Qed.

Lemma ℳ_top :
  forall {n : nat}, ℳ [ ⊤ ] <= n.
Proof.
  intros;
    simpl;
    crush.
Qed.

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
Qed.

Inductive restricted : ty -> Prop :=
| rest_top : restricted (⊤)
| rest_bnd : forall n, restricted (ρ̇ n)
| rest_hole : forall n, restricted (ρ♢ n)
| rest_arr : forall τ1 τ2, restricted τ1 ->
                      restricted τ2 ->
                      restricted (τ1 ⟶ τ2).

Fixpoint weight {n : nat}(Γ : env n)(τ : ty) :=
  match τ with
  | ⊤ => 0
  | 
  | τ1 ⟶ τ2 => max (weight Γ τ1) (weight Γ τ2)
  | (∀ τ1 ∙ τ2) => weight Γ τ1
  end.

Lemma ℳ_all :
  forall {τ : ty}{n : nat}, ℳ [τ] <= n ->
                     forall {x : nat}, ℳ [[x ↦ n]τ] <= S n.
Proof.
Qed.

Reserved Notation "Γ '⊢' τ1 '⩽' τ2"(at level 40).

Inductive sub {n : nat}: env n -> indexed_ty n -> indexed_ty n -> Prop :=
| s_top : forall Γ ι,
    Γ ⊢ ι ⩽ (⟦ ⊤ ⊨ ℳ_top⟧)

| s_rfl : forall Γ m (P : ℳ [α̇ m] <= n),
    Γ ⊢ ⟦ α̇ m ⊨ P ⟧ ⩽ ⟦ α̇ m ⊨ P ⟧

| s_var1 : forall Γ m ι1 ι2 (P : [m ⩽ ι1] ∈ Γ),
    Γ ⊢ ι1 ⩽ ι2 ->
    Γ ⊢ ⟦ (ρ̇ m) ⊨ get_le_ρ P ⟧ ⩽ ι2

| s_var2 : forall Γ m ι1 ι2 (P : [m ⩽ ι1] ∈ Γ),
    Γ ⊢ ι1 ⩽ ι2 ->
    Γ ⊢ ⟦ (υ̇ m) ⊨ get_le_υ P ⟧ ⩽ ι2

| s_all_kernel : forall (Γ : env n) (τ τ1 τ2 : ty)
                   (P1 : ℳ [ τ1] <= n)(P2 : ℳ [τ2] <= n)
                   (P : ℳ [τ] <= n),
    @sub (S n) (Γ , [n ⩽ (⟦ τ ⊨ P ⟧) ]) (⟦[0 ↦ n] τ1 ⊨ ℳ_sbst P1⟧) (⟦[0 ↦ n] τ2 ⊨ ℳ_sbst P2⟧) ->
    Γ ⊢ (⟦(∀ τ ∙ τ1) ⊨ ⟧) ⩽ (⟦(∀ τ ∙ τ2)⊨ ⟧)

| s_all : forall (Γ : env n) (τ1 τ2 τ1' τ2' : ty)
            (P1 : ℳ [ τ1] <= n)(P2 : ℳ [τ2] <= n)
            (P1' : ℳ [ τ1'] <= n)(P2' : ℳ [τ2'] <= n)
            ι1 ι2 (ι1' ι2' : indexed_ty (S n)),
    Γ ⊢ (⟦ τ2 ⊨ P2 ⟧) ⩽ (⟦ τ1 ⊨ P1 ⟧) ->
    @sub (S n) (Γ , [n ⩽ (⟦ τ2 ⊨ P2 ⟧) ]) (⟦[0 ↦ n] τ1' ⊨ ℳ_sbst P1'⟧) (⟦[0 ↦ n] τ2' ⊨ ℳ_sbst P2'⟧) ->
    Γ ⊢ ι1 ⩽ ι2

where "Γ '⊢' τ1 '⩽' τ2" := (sub Γ τ1 τ2).

Hint Constructors sub : f_sub_db.

Lemma closed_sbst :
  forall τ n, closed τ n ->
         forall n', n = S n' ->
               forall m, closed ([n' ↦ m] τ) n'.
Proof.
  intros τ n Hcl;
    induction Hcl;
    intros;
    simpl;
    subst;
    auto with f_sub_db.

  - eq_auto m n'; eauto with f_sub_db.
    crush.
Qed.

Lemma sbst_closed :
  forall τ n, closed τ n ->
         forall n' m, n' >= n ->
                 [n' ↦ m] τ = τ.
Proof.
  intros τ n Hcl;
    induction Hcl;
    intros;
    auto.

  - assert (m < n');
      [crush|].
    simpl.
    repeat eqb_auto;
      auto.

  - simpl.
    rewrite IHHcl1; auto.
    rewrite IHHcl2; crush.
Qed.
                    
Fixpoint sbst_n (min n : nat)(m : nat)(τ : ty) : ty :=
  if (min <=? n)
  then match n with
       | 0 => [n ↦ m] τ
       | S n' => sbst_n min n' (S m) ([n ↦ m] τ)
       end
  else τ.

Lemma sbst_le :
  forall min n m τ, min <= n ->
               sbst_n min n m τ = match n with
                                  | 0 => [n ↦ m] τ
                                  | S n' => sbst_n min n' (S m) ([n ↦ m] τ)
                                  end.
Proof.
  intros;
    destruct n;
    simpl;
    auto;
    rewrite leb_correct; auto.
Qed.

Lemma sbst_gt :
  forall min n m τ, min > n ->
               sbst_n min n m τ = τ.
Proof.
  intros;
    destruct n;
    simpl;
    auto;
    rewrite leb_correct_conv; auto.
Qed.

Lemma sbst_nle :
  forall min n m τ, ~ min <= n ->
               sbst_n min n m τ = τ.
Proof.
  intros;
    destruct n;
    simpl;
    auto;
    rewrite leb_correct_conv; crush.
Qed.

Lemma sbst_n_top :
  forall n min m, sbst_n min n m (⊤) = ⊤.
Proof.
  intros n;
    induction n;
    intros;
    simpl;
    try rewrite IHn.

  - destruct (min <=? 0);
      auto.

  - destruct (min <=? S n);
      auto.

Qed.

Lemma sbst_n_bnd :
  forall n min m x, sbst_n min n m (α x) = α x.
Proof.
  intros n;
    induction n;
    intros;
    simpl in *;
    eauto;
    try rewrite IHn.

  - destruct (min <=? 0);
      auto.

  - destruct (min <=? S n);
      auto.
Qed.

Hint Rewrite sbst_n_top sbst_n_bnd : f_sub_db.

Lemma sbst_n_hole_lt :
  forall n min m x, x < min -> sbst_n min n m (♢ x) = ♢ x.
Proof.
  intros n;
    induction n;
    intros;
    simpl in *;
    eauto.

  - eq_auto min 0;
      auto.
    assert (Hgt : min > 0);
      [crush
      |rewrite leb_correct_conv];
      crush.

  - eq_auto x (S n);
      try rewrite IHn;
      auto.
    + rewrite leb_correct_conv;
        crush.
    + destruct (min <=? S n);
        auto.

Qed.

Lemma sbst_n_hole_gt :
  forall n min m x, x > n -> sbst_n min n m (♢ x) = ♢ x.
Proof.
  intros n;
    induction n as [|n'];
    intros;
    let Hneq := fresh in
    match goal with
    | [Hgt : ?x > ?n |- _] =>
      assert (Hneq : x <> n);
        [crush|apply Nat.eqb_neq in Hneq]
    end;
    simpl;
    try rewrite Hneq.

  - destruct (min <=? 0);
      auto.

  - destruct (min  <=? S n');
      auto.
    rewrite IHn'; crush.
Qed.

Lemma sbst_n_hole_ge_le :
  forall n min m x, min <= x ->
               x <= n ->
               exists m', sbst_n min n m (♢ x) = α m' /\
                     m <= m.
Proof.
  intros n;
    induction n;
    intros;
    repeat eqb_auto;
    simpl.

  - assert (x = 0);
      [crush|subst].
    assert (min = 0);
      [crush|subst].
    simpl;
      repeat eexists;
      eauto.

  - assert (min <= S n);
      [crush|rewrite leb_correct; auto].
    eq_auto x (S n).
    + rewrite sbst_n_bnd.
      repeat eexists;
        eauto.
    + destruct (IHn min (S m) x) as [m'];
        auto;
        [crush|and_destruct].
      repeat eexists;
        crush.
Qed.

Lemma sbst_n_all :
  forall n min m τ1 τ2, sbst_n min n m (∀ τ1 ∙ τ2) = (∀ sbst_n min n m τ1 ∙ sbst_n (S min) (S n) m τ2).
Proof.
  intros n;
    induction n;
    intros.

  - simpl; destruct (min <=? 0); auto.

  - destruct (dec_le min (S n)).
    + rewrite sbst_le; auto.
      rewrite (sbst_le min (S n)); auto.
      rewrite (sbst_le (S min) (S (S n))); crush.
    + repeat rewrite sbst_nle; auto.
      crush.
Qed.



(*Lemma sbst_n_closed :
  forall n τ, closed τ n ->
         forall n' min m, n <= min ->
                     sbst_n min n' m τ = τ.
Proof.
  intros n;
    induction n;
    intros.
Qed.
      

Lemma sbst_Sn :
  forall n min m τ, closed τ n ->
               sbst_n min n m τ = [ min ↦ (m + n - min)] (sbst_n (S min) n m τ).
Proof.
  intros n;
    induction n;
    intros.

  - destruct (dec_le min 0).
    + simpl;
        repeat eqb_auto.
      assert (min = 0);
        [crush|subst].
      rewrite Nat.sub_0_r, Nat.add_0_r; auto.
    + simpl; rewrite leb_correct_conv; [|crush].
      erewrite sbst_closed; eauto.
      crush.

  - simpl.
    rewrite IHn.
    + destruct (dec_le min (S n));
        [rewrite (leb_correct min (S n)); auto|].
      * destruct (Nat.eq_dec min (S n));
          [subst|].
        ** rewrite sbst_closed with (τ:=τ)(n:=S n); auto.
        

Qed.

Lemma subtype_reflexivity :
  forall τ n, closed τ (S n) ->
         forall (Γ : env n),
           Γ ⊢ (sbst_n 0 n 0 τ) ⩽ (sbst_n 0 n 0 τ).
Proof.
  intros τ;
    induction τ;
    intros;
    try solve [eauto with f_sub_db].

  - rewrite sbst_n_top;
      auto with f_sub_db.

  - destruct v as [x|x];
      [|rewrite sbst_n_bnd; auto with f_sub_db].
    inversion H; subst.
    destruct (sbst_n_hole_ge_le n 0 0 x);
      crush.

  - rewrite sbst_n_all.
    inversion H; subst.
    apply s_all; eauto.
    apply IHτ2; auto.

  - match goal with
    | [Hcl : closed _ _ |- _] =>
      inversion Hcl;
        subst
    end.
    apply s_all;
      eauto.
    
Qed.


Lemma subtype_reflexivity :
  forall τ, (closed τ 0 \/ exists n m, ) ->
         forall (Γ : env n),
           Γ ⊢ (sbst_n n 0 τ) ⩽ (sbst_n n 0 τ).
Proof.
  intros τ;
    induction τ;
    intros;
    try solve [eauto with f_sub_db].

  - rewrite sbst_n_top;
      auto with f_sub_db.

  - destruct v as [x|x];
      [|rewrite sbst_n_bnd; auto with f_sub_db].
    destruct (le_gt_dec x n);
      [|rewrite sbst_n_hole_gt; auto].
    + let n' := fresh "n" in
      destruct (sbst_n_hole_le n 0 x) as [n'];
        auto;
        and_destruct.
      crush.
    + inversion H; subst; crush.

  - match goal with
    | [Hcl : closed _ _ |- _] =>
      inversion Hcl;
        subst;
        auto with f_sub_db
    end.
    crush.

  - match goal with
    | [Hcl : closed _ _ |- _] =>
      inversion Hcl;
        subst
    end.
    apply s_all;
      eauto.
    
Qed.*)
