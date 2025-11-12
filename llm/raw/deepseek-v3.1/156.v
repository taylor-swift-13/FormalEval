
Require Import String.
Require Import ZArith.

Definition int_to_mini_roman_spec (number : Z) (result : string) : Prop :=
  1 <= number <= 1000 /\
  result = 
    (match number / 1000 with
     | 0 => ""
     | _ => "m"
     end) ++
    (match (number mod 1000) / 100 with
     | 0 => ""
     | 1 => "c"
     | 2 => "cc"
     | 3 => "ccc"
     | 4 => "cd"
     | 5 => "d"
     | 6 => "dc"
     | 7 => "dcc"
     | 8 => "dccc"
     | _ => "cm"
     end) ++
    (match (number mod 100) / 10 with
     | 0 => ""
     | 1 => "x"
     | 2 => "xx"
     | 3 => "xxx"
     | 4 => "xl"
     | 5 => "l"
     | 6 => "lx"
     | 7 => "lxx"
     | 8 => "lxxx"
     | _ => "xc"
     end) ++
    (match number mod 10 with
     | 0 => ""
     | 1 => "i"
     | 2 => "ii"
     | 3 => "iii"
     | 4 => "iv"
     | 5 => "v"
     | 6 => "vi"
     | 7 => "vii"
     | 8 => "viii"
     | _ => "ix"
     end).
