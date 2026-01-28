Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Open Scope string_scope.
Import ListNotations.

Definition is_uppercase_vowel_bool (c : ascii) : bool :=
  match c with
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition count_upper_impl (s : string) : nat :=
  length (filter (fun i : nat =>
    match String.get i s with
    | Some c => andb (Nat.even i) (is_uppercase_vowel_bool c)
    | None => false
    end) (seq 0 (String.length s))).

Definition problem_98_pre (s : string) : Prop := True.

Definition problem_98_spec (s : string) (output : nat) : Prop :=
  output = count_upper_impl s.

Example problem_98_example :
  problem_98_spec "yfUFjyNNsqqpPazeMePJwoSMqrdxvQZaGTqVsxzvGn" 1.
Proof.
  unfold problem_98_spec, count_upper_impl.
  simpl.
  (* String.length "yfUFjyNNsqqpPazeMePJwoSMqrdxvQZaGTqVsxzvGn" = 43 *)
  (* seq 0 43 = [0;1;2;...;42] *)
  (* Evaluate the filter predicate for each index: *)
  (* We seek indices i where i is even and the character at i is an uppercase vowel: A, E, I, O, U *)
  (* Check character at even indices: *)

  (* i=0: 'y' lowercase -> false *)
  (* i=2: 'U' uppercase vowel -> true *)
  (* i=4: 'j' lowercase -> false *)
  (* i=6: 'N' uppercase but not vowel -> false *)
  (* i=8: 's' lowercase -> false *)
  (* i=10:'q' lowercase -> false *)
  (* i=12:'a' lowercase -> false *)
  (* i=14:'e' lowercase -> false *)
  (* i=16:'P' uppercase but not vowel -> false *)
  (* i=18:'w' lowercase -> false *)
  (* i=20:'S' uppercase but not vowel -> false *)
  (* i=22:'q' lowercase -> false *)
  (* i=24:'d' lowercase -> false *)
  (* i=26:'v' lowercase -> false *)
  (* i=28:'Q' uppercase but not vowel -> false *)
  (* i=30:'Z' uppercase but not vowel -> false *)
  (* i=32:'T' uppercase but not vowel -> false *)
  (* i=34:'V' uppercase but not vowel -> false *)
  (* i=36:'x' lowercase -> false *)
  (* i=38:'v' lowercase -> false *)
  (* i=40:'G' uppercase but not vowel -> false *)
  (* i=42:'n' lowercase -> false *)

  (* Only index 2 matches, so length = 1 *)
  reflexivity.
Qed.