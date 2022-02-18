package main

import "fmt"

/*
let c = newchan_int in
spawn (uf. (send 35 to c; f));
recv from c + recv from c + recv from c
*/

func sendloop(i int, ch chan int) {
	for {
		ch <- i
	}
}
func main() {
	ch := make(chan int)
	go sendloop(35, ch)
	fmt.Println(<-ch + <-ch + <-ch)
}
