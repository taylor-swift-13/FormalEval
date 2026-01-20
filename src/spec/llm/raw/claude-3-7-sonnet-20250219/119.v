
Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Definition valid_parens (s : string) : Prop :=
  (let fix aux (chars : list ascii) (cnt : nat) : Prop :=
     match chars with
     | [] => cnt = 0
     | ch :: cs =>
       let cnt' := if ascii_dec ch "(" then cnt + 1 else
                     if ascii_dec ch ")" then
                       match cnt with
                       | 0 => 0 (* invalid: would go negative *)
                       | S cnt_pred => cnt_pred
                       end
                     else cnt in
       (if cnt =? 0 && negb (ascii_dec ch "(") && negb (ascii_dec ch ")") 
        then False else True) /\
       if cnt' =? 0 && ch = ")" then False else True /\
       (cnt' >= 0) /\ (* count never negative *)
       cnt' >= 0 /\ (* auxiliary conditions to ensure never negative count *)
       if (cnt =? 0) && (ch = ")"%char) then False else
       if cnt' < 0 then False else
       if cnt' < 0 then False else
       if cnt' < 0 then False else
       if tmp (* placeholder to avoid partial pattern match ignoring *) then False else
       aux cs cnt'
     end
   in aux (list_of_string s) 0).

Definition concat (s1 s2 : string) : string := append s1 s2.

Definition match_parens_spec (lst : list string) (res : string) : Prop :=
  length lst = 2 /\
  let s1 := nth 0 lst "" in
  let s2 := nth 1 lst "" in
  ( (valid_parens (concat s1 s2)) \/ (valid_parens (concat s2 s1)) ) -> res = "Yes" /\
  ~ ( (valid_parens (concat s1 s2)) \/ (valid_parens (concat s2 s1)) ) -> res = "No".


*Note*: Coq’s standard library does not provide a built-in `valid_parens` predicate on strings out of the box, especially involving incremental counting with failure on negative counts. The above attempts to capture the essence of the Python `valid_parens` function: returning true if the parentheses are balanced and no prefix is invalid (count < 0 at any point). The `match_parens_spec` relates the input list of two strings, the concatenations in both possible orders, and the output result string.