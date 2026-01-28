Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Definition swap_case (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if andb (leb 65 n) (leb n 90)
  then ascii_of_nat (n + 32)
  else if andb (leb 97 n) (leb n 122)
  then ascii_of_nat (n - 32)
  else c.

Definition replace_vowel (c : ascii) : ascii :=
  match c with
  | "a"%char => "c"%char | "e"%char => "g"%char | "i"%char => "k"%char | "o"%char => "q"%char | "u"%char => "w"%char
  | "A"%char => "C"%char | "E"%char => "G"%char | "I"%char => "K"%char | "O"%char => "Q"%char | "U"%char => "W"%char
  | _ => c
  end.

Definition encode_char_spec (c_in c_out : ascii) : Prop :=
  let c_swapped := swap_case c_in in
  if is_vowel c_in
  then c_out = replace_vowel c_swapped
  else c_out = c_swapped.

Definition problem_93_pre (s_in : string) : Prop :=
  let l_in := list_ascii_of_string s_in in
  Forall (fun c => let n := nat_of_ascii c in (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122) \/ n = 32) l_in.

Definition problem_93_spec (s_in s_out : string) : Prop :=
  let l_in := list_ascii_of_string s_in in
  let l_out := list_ascii_of_string s_out in
  Forall2 encode_char_spec l_in l_out.

Example encode_alphabet_spec :
  problem_93_spec "abcdefghijklmnopqrstuvwxyz" "CBCDGFGHKJKLMNQPQRSTWVWXYZ".
Proof.
  unfold problem_93_spec.
  simpl.
  constructor. (* a -> C *)
  - unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
    simpl.
    reflexivity.
  - constructor. (* b -> B *)
    + unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
      simpl.
      reflexivity.
    + constructor. (* c -> C *)
      * unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
        simpl.
        reflexivity.
      * constructor. (* d -> D *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* e -> G *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* f -> F *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* g -> G *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* h -> H *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* i -> K *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* j -> J *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* k -> K *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* l -> L *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* m -> M *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* n -> N *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* o -> Q *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* p -> P *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* q -> Q *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* r -> R *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* s -> S *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* t -> T *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* u -> W *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* v -> V *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* w -> W *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* x -> X *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* y -> Y *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor. (* z -> Z *)
        { unfold encode_char_spec, swap_case, is_vowel, replace_vowel.
          simpl.
          reflexivity.
        }
        constructor.
Qed.