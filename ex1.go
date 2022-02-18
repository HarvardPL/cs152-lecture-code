package main

import "fmt"

/*
let c = newchan_int in
spawn (send 35 to c);
recv from c + 7
*/

func send(i int, ch chan int) {
	ch <- i
}
func main() {
	ch := make(chan int)
	go send(35, ch)
	i := <-ch
	fmt.Println(i + 7)
}
