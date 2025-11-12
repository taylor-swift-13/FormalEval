
Require Import String Ascii.
Require Import ZArith.

Definition correct_bracketing_spec (brackets : string) (result : bool) : Prop :=
  exists cnt : Z,
    (fix process_chars (s : string) (current_cnt : Z) : Z :=
       match s with
       | EmptyString => current_cnt
       | String c rest =>
           let new_cnt :=
               if ascii_dec c "<"%char then current_cnt + 1
               else if ascii_dec c ">"%char then current_cnt - 1
               else current_cnt
           in
           if new_cnt <? 0 then -1
           else process_chars rest new_cnt
       end) brackets 0 = cnt ∧
    (cnt <? 0 -> result = false) ∧
    (cnt >= 0 -> result = (cnt =? 0)).
