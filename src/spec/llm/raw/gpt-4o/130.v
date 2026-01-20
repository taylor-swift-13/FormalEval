
Require Import List ZArith.

Definition tri_spec (n : Z) (seq : list Z) : Prop :=
  n >= 0 /\
  (n = 0 -> seq = [1]) /\
  (n = 1 -> seq = [1; 3]) /\
  (n >= 2 ->
    seq = 
      let fix tribonacci (i : Z) (acc : list Z) : list Z :=
        match i with
        | 0 => acc
        | _ =>
          let new_elem :=
            if Z.even i then
              1 + i / 2
            else
              (nth (Z.to_nat (i - 1)) acc 0) +
              (nth (Z.to_nat (i - 2)) acc 0) +
              (1 + (i + 1) / 2)
          in
          tribonacci (i - 1) (acc ++ [new_elem])
        end
      in
      tribonacci n [1; 3]).
