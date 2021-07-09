Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive unit : Set :=
| tt.

Check unit.
Check tt.

Theorem unit_singleton : forall x : unit, x = tt.
  induction x. reflexivity.
Qed.

(* for non-recursive inductive types, destruct is enought *)

Check unit_ind.

Check (fun u : unit => u = tt).
Check (unit_ind (fun u : unit => u = tt)).

Inductive Empty_set : Set :=.

Theorem the_sky_is_falling : forall x : Empty_set, 2 + 2 = 5.
  destruct 1.
Qed.

Check Empty_set_ind.

Definition e2u (e : Empty_set) : unit := match e with end.

Inductive bool : Set :=
| true
| false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition negb' (b : bool) : bool :=
  if b then false else true.

Theorem negb_inverse : forall b : bool, negb (negb b) = b.
  destruct b. reflexivity.
  Restart.
  destruct b; reflexivity.
Qed.

Theorem negb_ineq : forall b : bool, negb b <> b.
  destruct b; discriminate.
  (* two values of an inductive type are not equal *)
Qed.

Check bool_ind.

(* the curry howard version is not interesting *)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Definition isZero (n : nat) : bool :=
  match n with
  | O => true
  | S _  => false
  end.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Theorem O_plus_n : forall n : nat, plus O n = n.
  intros. simpl. reflexivity.
Qed.

Theorem n_plus_O : forall n : nat, plus n O = n.
  induction n.
  reflexivity.
  simpl. rewrite IHn.
  reflexivity.
  Restart.
  induction n; crush.
Qed.

Check nat_ind.

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
  injection 1. trivial.
Qed.

(* congruence is a complete decision procedure for the theory of equality and uninterpreted functions,
   plus some smarts about inductive types *)

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
  | NNil => O
  | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
  | NNil => ls2
  | NCons n ls1' => NCons n (napp ls1' ls2)
  end.

Theorem nlength_napp : forall ls1 ls2 : nat_list,
    nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2).
Proof.
  induction ls1; crush.
Qed.

Check nat_list_ind.

Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Check nat_btree_ind.

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
  | NLeaf => S O
  | NNode tr1 _ tr2 => plus (nsize tr1) (nsize tr2)
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) : nat_btree :=
  match tr1 with
  | NLeaf => NNode tr2 O NLeaf
  | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Section list.
  Variable T : Set.

  Inductive list : Set :=
  | Nil : list
  | Cons : T -> list -> list.

  Fixpoint length (ls : list) : nat :=
    match ls with
    | Nil => O
    | Cons _ ls' => S (length ls')
    end.

  Fixpoint app (ls1 ls2 : list) : list :=
    match ls1 with
    | Nil => ls2
    | Cons x ls1' => Cons x (app ls1' ls2)
    end.
End list.

Arguments Nil {T}.

Print list.

Check Cons.

Inductive even_list : Set :=
| ENil : even_list
| ECons : nat -> odd_list -> even_list
with odd_list : Set :=
| OCons : nat -> even_list -> odd_list.

Fixpoint elength (el : even_list) : nat :=
  match el with
  | ENil => O
  | ECons _ ol => S (olength ol)
  end
with olength (ol : odd_list) : nat :=
       match ol with
       | OCons _ el => S (elength el)
       end.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
  | ENil => el2
  | ECons n ol => ECons n (oapp ol el2)
  end
with oapp (ol : odd_list) (el : even_list) : odd_list :=
       match ol with
       | OCons n el' => OCons n (eapp el' el)
       end.

Theorem elength_eapp: forall el1 el2 : even_list,
    elength (eapp el1 el2) = plus (elength el1) (elength el2).
Proof.
  induction el1; crush.
  f_equal.
Abort.

Check even_list_ind.

Scheme even_list_mut := Induction for even_list Sort Prop
  with odd_list_mut := Induction for odd_list Sort Prop.

Check even_list_mut.

Theorem n_plus_O' : forall n : nat, plus n O = n.
  apply nat_ind.
  Undo.
  apply (nat_ind (fun n => plus n O = n)); crush.
Qed.

Inductive pformula : Set :=
| Truth : pformula
| Falsehood : pformula
| Conjunction : pformula -> pformula -> pformula.

Fixpoint pformulaDenote (f : pformula) : Prop :=
  match f with
  | Truth => True
  | Falsehood => False
  | Conjunction f1 f2 => pformulaDenote f1 /\ pformulaDenote f2
  end.

Inductive formula : Set :=
| Eq : nat -> nat -> formula
| And : formula -> formula -> formula
| Forall : (nat -> formula) -> formula.

Example forall_refl : formula := Forall (fun x => Eq x x).

Fixpoint formulaDenote (f : formula) : Prop :=
  match f with
  | Eq n1 n2 => n1 = n2
  | And f1 f2 => formulaDenote f1 /\ formulaDenote f2
  | Forall f' => forall n : nat, formulaDenote (f' n)
  end.

Fixpoint swapper (f : formula) : formula :=
  match f with
  | Eq n1 n2 => Eq n2 n1
  | And f1 f2 => And (swapper f2) (swapper f1)
  | Forall f' => Forall (fun n => swapper (f' n))
  end.
