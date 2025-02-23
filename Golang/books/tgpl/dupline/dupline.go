// 示例: 查找文件中重复行
package main

import (
	"fmt"
	"io/ioutil"
	"log"
	"os"
	"strings"
)

func init() {
	// log.SetFlags(log.Ldate | log.Ltime | log.Llongfile)
	log.SetFlags(log.Ldate | log.Ltime | log.Lshortfile)
}

func main() {
	counts := make(map[string]int)
	for _, filename := range os.Args[1:] {
		dupline(filename, counts)
	}

	for line, n := range counts {
		if n > 1 {
			log.Printf("%d\t%s\n", n, line)
		}
	}
}

func dupline(filename string, counts map[string]int) error {
	data, err := ioutil.ReadFile(filename)
	if err != nil {
		return fmt.Errorf("dup: %v\n", err)
	}
	dup(string(data), counts)
	return nil
}

func dup(content string, counts map[string]int) {
	for _, line := range strings.Split(string(content), "\n") {
		counts[line]++
	}
}
