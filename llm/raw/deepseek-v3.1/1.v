
Require Import List String Ascii.
Import ListNotations.

Definition separate_paren_groups_spec (paren_string : string) (results : list string) : Prop :=
  exists cnt group : nat,
    let fix process (s : string) (cnt group_idx : nat) (acc : list string) : list string :=
      match s with
      | "" => acc
      | String ch rest =>
          let new_cnt := match ch with
                        | "(" => S cnt
                        | ")" => pred cnt
                        | _ => cnt
                        end in
          let new_group_idx := if ascii_dec ch " " then group_idx else group_idx + 1 in
          if new_cnt =? 0 then
            if group_idx >? 0 then
              process rest new_cnt 0 (acc ++ [substring (group_idx - new_group_idx) new_group_idx paren_string])
            else
              process rest new_cnt 0 acc
          else
            process rest new_cnt new_group_idx acc
      end in
    results = process paren_string 0 0 [].
