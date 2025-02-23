package links

import (
	"bytes"

	"golang.org/x/net/html"
)

func CollectLinks(body []byte) ([]string, error) {
	doc, err := html.Parse(bytes.NewReader(body))
	if err != nil {
		return nil, err
	}

	return visit(nil, doc), nil
}

// 收集HTML节点中的链接
func visit(links []string, n *html.Node) []string {
	// 当前元素
	if n.Type == html.ElementNode && n.Data == "a" {
		for _, a := range n.Attr {
			if a.Key == "href" {
				links = append(links, a.Val)
			}
		}
	}
	// 子元素
	for c := n.FirstChild; c != nil; c = c.NextSibling {
		links = visit(links, c) // 递归调用
	}
	return links
}

// 广度优先遍历: 在工作表worklist的元素上应用函数f后添加到工作表中
func breadFirst(f func(item string) []string, worklist []string) {
	seen := make(map[string]bool)
	for len(worklist) > 0 {
		items := worklist
		worklist = nil
		for _, item := range items {
			if !seen[item] {
				seen[item] = true
				worklist = append(worklist, f(item)...)
			}
		}
	}
}
