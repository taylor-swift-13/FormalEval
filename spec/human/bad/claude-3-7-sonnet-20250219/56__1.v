Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Open Scope string_scope.

(* The given inductive definition *)
Inductive is_correctly_bracketed : string -> Prop :=
  | cb_nil    : is_correctly_bracketed ""
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("<" ++ l ++ ">")
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

Definition list_ascii_of_string (s : string) : list ascii :=
  fix aux s :=
    match s with
    | EmptyString => nil
    | String c s' => c :: aux s'
    end s.

Definition problem_56_pre (brackets : string) : Prop :=
  Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

(* Boolean decidable equality of ascii characters *)
Definition ascii_eqb (a b: ascii) : bool :=
  if ascii_dec a b then true else false.

Fixpoint correct_bracketing_aux (stack : nat) (s : string) : bool :=
  match s with
  | EmptyString => Nat.eqb stack 0
  | String c s' =>
    if ascii_eqb c "<"%char then
      correct_bracketing_aux (S stack) s'
    else if ascii_eqb c ">"%char then
      match stack with
      | 0 => false
      | S n => correct_bracketing_aux n s'
      end
    else false
  end.

Definition correct_bracketing (s : string) : bool :=
  correct_bracketing_aux 0 s.

Example test_correct_bracketing_1 :
  problem_56_spec "<>" true.
Proof.
  unfold problem_56_spec, correct_bracketing.
  simpl.
  unfold correct_bracketing_aux.
  (* Step 1: first character '<' *)
  simpl.
  (* ascii_eqb "<" "<" = true *)
  unfold ascii_eqb.
  destruct (ascii_dec "<" "<") as [_|n]; [|discriminate].
  simpl.
  (* recursive call with stack = 1 and string = ">" *)
  fold (correct_bracketing_aux 1 ">" ).
  unfold ascii_eqb.
  destruct (ascii_dec ">" "<") as [H|H].
  - discriminate.
  - destruct (ascii_dec ">" ">") as [_|H].
    + simpl.
      (* stack = 1, so move to stack = 0 *)
      destruct 1; [discriminate|].
      fold (correct_bracketing_aux 0 "").
      simpl.
      (* stack=0 and empty string -> true *)
      apply Nat.eqb_refl.
    + discriminate.
Qed.