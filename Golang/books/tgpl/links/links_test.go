package links

import (
	"fmt"
	"log"
	"os"
	"testing"
	"time"
)

func testFetchOne(t *testing.T) {
	url := "https://godoc.org/fmt"
	body := string(Fetch(url))
	fmt.Println(body)
}

func testFetchByChannel(t *testing.T) {
	start := time.Now()
	ch := make(chan string)
	for _, url := range os.Args[1:] {
		go FetchByChannel(url, ch)
	}
	for range os.Args[1:] {
		log.Println(<-ch)
	}
	log.Printf("%.2fs elapsed\n", time.Since(start).Seconds())
}

func testCollectLinks(t *testing.T) {
	url := "https://godoc.org/fmt"
	links, err := CollectLinks(Fetch(url))
	if err != nil {
		t.Error(err)
	}
	for _, link := range links {
		fmt.Println(link)
	}
}

func testOutline(t *testing.T) {
	url := "https://godoc.org/fmt"
	Outline(Fetch(url))
}

func TestForEachNode(t *testing.T) {
	url := "https://godoc.org/fmt"
	doc, err := FetchNode(url)
	if err != nil {
		t.Error(err)
	}

	forEachNode(doc, startElement, endElement)
}
