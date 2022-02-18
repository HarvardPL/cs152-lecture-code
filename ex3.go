package main

import "fmt"

/*
let c = newchan_int in
spawn (3 + recv from c);
spawn (5 + recv from c);
send 15 to c
*/

func recv(i int, ch chan int, quit chan bool) {
	v := <-ch
	fmt.Println(i + v)
	<-quit
}
func main() {
	ch := make(chan int)
	quit := make(chan bool)
	go recv(3, ch, quit)
	go recv(5, ch, quit)
	ch <- 15
	quit <- true
}
