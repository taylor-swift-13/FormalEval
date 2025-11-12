
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.

Definition valid_range (number : nat) : Prop :=
  1 <= number <= 1000.

Definition int_to_mini_roman_spec (number : nat) (roman : string) : Prop :=
  valid_range number /\
  (forall m c x i thousands hundreds tens ones : string,
      m = "" \/ m = "m" ->
      c = "" \/ c = "c" \/ c = "cc" \/ c = "ccc" \/ c = "cd" \/ c = "d" \/ c = "dc" \/ c = "dcc" \/ c = "dccc" \/ c = "cm" ->
      x = "" \/ x = "x" \/ x = "xx" \/ x = "xxx" \/ x = "xl" \/ x = "l" \/ x = "lx" \/ x = "lxx" \/ x = "lxxx" \/ x = "xc" ->
      i = "" \/ i = "i" \/ i = "ii" \/ i = "iii" \/ i = "iv" \/ i = "v" \/ i = "vi" \/ i = "vii" \/ i = "viii" \/ i = "ix" ->
      thousands = m /\
      hundreds = c /\
      tens = x /\
      ones = i /\
      thousands = if Nat.leb 1 (number / 1000) then "m" else "" /\
      hundreds = match (number mod 1000) / 100 with
                 | 0 => ""
                 | 1 => "c"
                 | 2 => "cc"
                 | 3 => "ccc"
                 | 4 => "cd"
                 | 5 => "d"
                 | 6 => "dc"
                 | 7 => "dcc"
                 | 8 => "dccc"
                 | 9 => "cm"
                 | _ => "" (* impossible case *)
                 end /\
      tens = match (number mod 100) / 10 with
             | 0 => ""
             | 1 => "x"
             | 2 => "xx"
             | 3 => "xxx"
             | 4 => "xl"
             | 5 => "l"
             | 6 => "lx"
             | 7 => "lxx"
             | 8 => "lxxx"
             | 9 => "xc"
             | _ => "" (* impossible case *)
             end /\
      ones = match (number mod 10) with
             | 0 => ""
             | 1 => "i"
             | 2 => "ii"
             | 3 => "iii"
             | 4 => "iv"
             | 5 => "v"
             | 6 => "vi"
             | 7 => "vii"
             | 8 => "viii"
             | 9 => "ix"
             | _ => "" (* impossible case *)
             end /\
      roman = String.append thousands (String.append hundreds (String.append tens ones))
  ).
