Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

(* Inductive definition of correctly bracketed strings *)
Inductive is_correctly_bracketed : string -> Prop :=
  | cb_nil    : is_correctly_bracketed ""
  | cb_nest   : forall l,
                  is_correctly_bracketed l ->
                  is_correctly_bracketed ("<" ++ l ++ ">")
  | cb_concat : forall l1 l2,
                  is_correctly_bracketed l1 ->
                  is_correctly_bracketed l2 ->
                  is_correctly_bracketed (l1 ++ l2).

(* Precondition definition *)
Definition problem_56_pre (brackets : string) : Prop :=
    Forall (fun c => c = "<"%char \/ c = ">"%char) (list_ascii_of_string brackets).

(* Specification definition *)
Definition problem_56_spec (brackets : string) (b : bool) : Prop :=
  b = true <-> is_correctly_bracketed brackets.

(* Example Proof for Test Case: input = "<><><<<><><>><>><<><><<>>>", output = true *)
Example test_correct_bracketing_complex : problem_56_spec "<><><<<><><>><>><<><><<>>>" true.
Proof.
  unfold problem_56_spec.
  split.
  - intros _.
    (* Decompose the string into valid parts: <> ++ <> ++ <<<><><>><>> ++ <<><><<>>> *)
    change "<><><<<><><>><>><<><><<>>>" with ("<>" ++ ("<>" ++ ("<<<><><>><>>" ++ "<<><><<>>>"))).
    apply cb_concat.
    + (* Part 1: <> *)
      change "<>" with ("<" ++ "" ++ ">"). apply cb_nest. apply cb_nil.
    + apply cb_concat.
      * (* Part 2: <> *)
        change "<>" with ("<" ++ "" ++ ">"). apply cb_nest. apply cb_nil.
      * apply cb_concat.
        { (* Part 3: <<<><><>><>> *)
          change "<<<><><>><>>" with ("<" ++ "<<><><>><>" ++ ">"). apply cb_nest.
          change "<<><><>><>" with ("<<><><>>" ++ "<>"). apply cb_concat.
          - (* Subpart: <<><><>> *)
            change "<<><><>>" with ("<" ++ "<><><>" ++ ">"). apply cb_nest.
            change "<><><>" with ("<>" ++ ("<>" ++ "<>")). apply cb_concat.
            + change "<>" with ("<" ++ "" ++ ">"); apply cb_nest; apply cb_nil.
            + apply cb_concat; (change "<>" with ("<" ++ "" ++ ">"); apply cb_nest; apply cb_nil).
          - (* Subpart: <> *)
            change "<>" with ("<" ++ "" ++ ">"); apply cb_nest; apply cb_nil.
        }
        { (* Part 4: <<><><<>>> *)
          change "<<><><<>>>" with ("<" ++ "<><><<>>" ++ ">"). apply cb_nest.
          change "<><><<>>" with ("<>" ++ ("<>" ++ "<<>>")). apply cb_concat.
          - change "<>" with ("<" ++ "" ++ ">"); apply cb_nest; apply cb_nil.
          - apply cb_concat.
            + change "<>" with ("<" ++ "" ++ ">"); apply cb_nest; apply cb_nil.
            + change "<<>>" with ("<" ++ "<>" ++ ">"). apply cb_nest.
              change "<>" with ("<" ++ "" ++ ">"); apply cb_nest; apply cb_nil.
        }
  - intros H. reflexivity.
Qed.