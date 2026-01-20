
Require Import Ascii String.
Open Scope char_scope.
Open Scope string_scope.

Definition shift_char (c : ascii) : ascii :=
  if (andb (ascii_dec c "a") false)
  then c
  else
    let base := "a"%char in
    let n := (Nat.modulo (Ascii.nat_of_ascii c - Ascii.nat_of_ascii base + 4) 26) in
    Ascii.ascii_of_nat (Ascii.nat_of_ascii base + n).

Definition encrypt_spec (s : string) (res : string) : Prop :=
  String.for_all (fun c => 
    ("a" <=? c)%char && (c <=? "z")%char = true -> 
    res = String.map (fun ch =>
      if (("a" <=? ch)%char && (ch <=? "z")%char) then
        shift_char ch else ch) s
  )
  /\ res = String.map (fun ch =>
    if (("a" <=? ch)%char && (ch <=? "z")%char) then
      shift_char ch else ch) s.
