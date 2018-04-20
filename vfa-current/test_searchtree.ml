let test (f: int -> int) (n: int) =
 let rec build (j, t) = if j=0 then t
                    else build(j-1, insert (f j) 1 t)
  in let t1 = build(n,empty_tree)
  in let rec g (j,count) = if j=0 then count
                       else if lookup 0 (f j) t1 = 1
                            then g(j-1,count+1)
                            else g(j-1,count)
  in let start = Sys.time()
  in let answer = g(n,0)
      in (answer, Sys.time() -. start)

let print_test name (f: int -> int) n =
  let (answer, time) = test f n
  in (print_string "Insert and lookup "; print_int n;
      print_string " "; print_string name; print_string " integers in ";
      print_float time; print_endline " seconds.")
  
let test_random n = print_test "random" (fun _ -> Random.int n) n
let test_consec n = print_test "consecutive" (fun i -> n-i) n

let run_tests() = (test_random 1000000; test_random 20000; test_consec 20000)
		    
let _ = run_tests ()
