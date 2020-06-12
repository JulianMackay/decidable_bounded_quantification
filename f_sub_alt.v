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

Inductive ty {n : nat} : nat -> Type :=
| top : ty n
| t_var : var -> ty n
| all : ty n -> ty (S n) -> ty n
| raise : ty n -> ty (S n).

Notation "'⊤'" := (top)(at level 40).
Notation "'♢' n" := (t_var (hole n))(at level 40).
Notation "'α' n" := (t_var (bnd n))(at level 40).
Notation "'∀' τ1 '∙' τ2" := (all τ1 τ2)(at level 40).
Notation "'↑' τ" := (raise τ)(at level 40).

Inductive indexed_option {A : nat -> Type}{n : nat} : Type :=
| Nothing : indexed_option
| Just : A n -> indexed_option.

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

Definition de_bruijn_map (A : nat -> Type)(n : nat) := nat -> A n.

Definition db_empty {A : nat -> Type}(a : A 0) : de_bruijn_map A 0 := (fun _ => a).

Definition db_update {A : nat -> Type}{n : nat}
           (r : A n -> A (S n))
           (a : A (S n))
           (Γ : de_bruijn_map A n) :
  de_bruijn_map A (S n) := fun m => if (eqb n m) then a else r (Γ m).

Definition env (n : nat) := de_bruijn_map (@indexed_option (@ty n)) n.

Definition empty : env 0 := db_empty Nothing.

Definition raise_mapping {n : nat}(m : @indexed_option ty n) : @indexed_option ty (S n) :=
  match m with
  | Nothing => Nothing
  | Just τ => Just (↑ τ)
  end.

Definition update {n : nat}(τ : (@ty n n))(Γ : env n) := @db_update (@indexed_option ty) n raise_mapping.

(*Definition partial_map (A : Type)`{Eq A}(B : Type) := total_map A (option B).

Definition empty {A B : Type} `{Eq A} : partial_map A B := t_empty None.

Definition update {A B : Type} `{Eq A} (a : A) (b : B) (map : partial_map A B) :=
  t_update map a (Some b).*)

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

Fixpoint sbst {n' : nat}(n m : nat)(τ : ty m) : ty (S m) :=
  match τ with
  | ♢ n' => if n' =? n
           then (α m)
           else ↑ τ
  | (∀ τ1 ∙ τ2) => (∀ (sbst n m τ1) ∙ (sbst (S n) m τ2))
  | raise τ' => raise (sbst n m τ')
  | ⊤ => ⊤
  | α _ => τ
  end.

Notation "'[' n '↦' m ']' τ":=(sbst n m τ)(at level 40).

Notation "'[' a '⩽' b ']' '∈' c" := (c a = Some b)(at level 40).

Notation "Γ ',' '[' n '⩽' τ ']'":=(@update n τ Γ)(at level 40).

Inductive finite {n : nat} : env n -> Prop :=
| fin_empty : finite empty
| fin_update : forall Γ τ, finite Γ ->
                      finite (Γ , [n ⩽ τ]).

Reserved Notation "Γ '⊢' τ1 '⩽' τ2"(at level 40).

Fixpoint max_n (τ : ty) : nat :=
  match τ with
  | ⊤ => 0
  | α n => n
  | (∀ τ1 ∙ τ2) => max (max_n τ1) (max_n τ2)
  | _ => 0
  end.

Notation "'ℳ' '[' τ ']'" := (max_n τ).

Fixpoint all_measure (τ : ty) :=
  match τ with
  | (∀ τ1 ∙ τ2) => 1 + (all_measure τ1) + (all_measure τ2)
  | _ => 0
  end.

Notation "'𝒜' '[' τ ']'" := (all_measure τ)(at level 40).



Inductive closed : ty -> nat -> Prop :=
| cl_bnd : forall n m, closed (α m) n
| cl_hole : forall n m, m < n ->
                   closed (♢ m) n
| cl_top : forall n, closed (⊤) n
| cl_all : forall n τ1 τ2, closed τ1 n ->
                      closed τ2 (S n) ->
                      closed (∀ τ1 ∙ τ2) n.

Hint Constructors closed : f_sub_db.

Inductive sub {n : nat} : env n -> ty -> ty -> Prop :=
| s_top : forall Γ τ, Γ ⊢ τ ⩽ ⊤
| s_rfl : forall Γ m, Γ ⊢ α m ⩽ α m
| s_var : forall Γ m τ1 τ2, [m ⩽ τ1] ∈ Γ ->
                       Γ ⊢ τ1 ⩽ τ2 ->
                       Γ ⊢ α m ⩽ τ2
| s_all : forall Γ τ1 τ2 τ1' τ2', Γ ⊢ τ2 ⩽ τ1 ->
                             Γ , [n ⩽ τ2] ⊢ ([0 ↦ n]τ1') ⩽ ([0 ↦ n]τ2') ->
                             Γ ⊢ (∀ τ1 ∙ τ1') ⩽ (∀ τ2 ∙ τ2')

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

Lemma sbst_n_closed :
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
    
Qed.
