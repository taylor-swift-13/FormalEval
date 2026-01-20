Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Import ListNotations.

Definition char_relation (c_in c_out : ascii) : Prop :=
  match c_in with
  | "a"%char => c_out = "e"%char | "b"%char => c_out = "f"%char | "c"%char => c_out = "g"%char | "d"%char => c_out = "h"%char
  | "e"%char => c_out = "i"%char | "f"%char => c_out = "j"%char | "g"%char => c_out = "k"%char | "h"%char => c_out = "l"%char
  | "i"%char => c_out = "m"%char | "j"%char => c_out = "n"%char | "k"%char => c_out = "o"%char | "l"%char => c_out = "p"%char
  | "m"%char => c_out = "q"%char | "n"%char => c_out = "r"%char | "o"%char => c_out = "s"%char | "p"%char => c_out = "t"%char
  | "q"%char => c_out = "u"%char | "r"%char => c_out = "v"%char | "s"%char => c_out = "w"%char | "t"%char => c_out = "x"%char
  | "u"%char => c_out = "y"%char | "v"%char => c_out = "z"%char | "w"%char => c_out = "a"%char | "x"%char => c_out = "b"%char
  | "y"%char => c_out = "c"%char | "z"%char => c_out = "d"%char
  | _ => c_out = c_in
  end.

Definition encrypt_spec (s : list ascii) (output : list ascii) : Prop :=
  Forall2 char_relation s output.

Example encrypt_test_bc_thequricertthelazydog :
  encrypt_spec ["b"%char; "c"%char; "&"%char; "t"%char; "h"%char; "e"%char; "q"%char; "u"%char; "r"%char; "i"%char; "c"%char; "e"%char; "r"%char; "t"%char; "t"%char; "h"%char; "e"%char; "l"%char; "a"%char; "z"%char; "y"%char; "d"%char; "o"%char; "g"%char; "^"%char; "%" %char]
               ["f"%char; "g"%char; "&"%char; "x"%char; "l"%char; "i"%char; "u"%char; "y"%char; "v"%char; "m"%char; "g"%char; "i"%char; "v"%char; "x"%char; "x"%char; "l"%char; "i"%char; "p"%char; "e"%char; "d"%char; "c"%char; "h"%char; "s"%char; "k"%char; "^"%char; "%" %char].
Proof.
  unfold encrypt_spec.
  repeat constructor; simpl; reflexivity.
Qed.