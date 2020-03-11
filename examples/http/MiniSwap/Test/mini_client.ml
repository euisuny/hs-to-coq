open Bytes;;
open Unix;;

let buf_size : int = 3

let timeout : float = 1.0

let port : int = 8500
let server_addr : inet_addr = Unix.inet_addr_loopback

let new_socket () : file_descr =
  let open Unix in
  let sock = socket PF_INET SOCK_STREAM 0 in
  connect sock (ADDR_INET (server_addr, port));
  set_nonblock sock;
  sock

let send_msg (sock : Unix.file_descr) (bs : bytes) : unit =
  ignore (Unix.send sock bs 0 (Bytes.length bs) [])

let recv_msg (sock : Unix.file_descr) : bytes =
  let bs = Bytes.create buf_size in
  let rec loop i j =
    match Unix.recv sock bs i j [] with
    | exception Unix.Unix_error(Unix.EAGAIN, _, _) ->
        loop i j
    | 0 -> Printf.printf "Oops.\n"; exit 1
    | k ->
      Printf.printf "%d...\n" k;
      if k = j then
        bs
      else
        loop (i + k) (j - k) in
  loop 0 buf_size

let send_byte (sock : file_descr) (c : char) : unit =
  send_msg sock (make 1 c)

let recv_obyte (sock : file_descr) : char option =
  let bs = Bytes.create 1 in
  match Unix.recv sock bs 0 1 [] with
  | exception Unix.Unix_error(Unix.EAGAIN, _, _) ->
     None
  | 0 -> None
  | k ->
     if k = 1 then
       Some (Bytes.get bs 0)
     else
       None

let mk_msg c = Bytes.make buf_size c

let close (sock : Unix.file_descr) : unit = Unix.shutdown sock Unix.SHUTDOWN_ALL

let test () =
  let s1 = new_socket () in
  let s2 = new_socket () in
  let s3 = new_socket () in
  let s4 = new_socket () in
  print_endline "connected";
  send_msg s1 (mk_msg 'a');
  send_msg s2 (mk_msg 'b');
  send_msg s3 (mk_msg 'c');
  print_endline "sent";
  Printf.printf "%c %c %c\n" (Bytes.get (mk_msg 'a') 0) (Bytes.get (mk_msg 'b') 0) (Bytes.get (mk_msg 'c') 0);
  close s4;
  let r1 = recv_msg s1 in
  let r2 = recv_msg s2 in
  let r3 = recv_msg s3 in
  close s1;
  close s2;
  close s3;
  Printf.printf "%c %c %c\n" (Bytes.get r1 0) (Bytes.get r2 0) (Bytes.get r3 0)

let test_2 () =
  let s1 = new_socket () in
  print_endline "connected";
  send_msg s1 (mk_msg 'a');
  print_endline "sent";
  let r1 = recv_msg s1 in
  close s1;
  Printf.printf "%c\n" (Bytes.get r1 0)

let _ = test ()
