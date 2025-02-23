// 示例: 包encoding/xml, 使用基于token的API提取元素
package main

import (
	"encoding/xml"
	"fmt"
	"io"
	"os"
	"strings"
)

// 测试输出:

/*

$ wget https://www.w3.org/TR/2006/REC-xml11-20060816/ -O - | ./xmlselect div div h2
--2019-10-23 17:31:24--  https://www.w3.org/TR/2006/REC-xml11-20060816/
Resolving www.w3.org (www.w3.org)... 128.30.52.100
Connecting to www.w3.org (www.w3.org)|128.30.52.100|:443... connected.
HTTP request sent, awaiting response... 200 OK
Length: 225335 (220K) [text/html]
Saving to: ‘STDOUT’

-                                             3%[==>                                                                                      ]   8.00K  14.3KB/s               html body div div h2: 1 Introduction
-                                            10%[========>                                                                                ]  24.00K  23.5KB/s               html body div div h2: 2 Documents
-                                            25%[=====================>                                                                   ]  56.00K  27.3KB/s               html body div div h2: 3 Logical Structures
html body div div h2: 4 Physical Structures  47%[=========================================>                                               ] 104.00K  27.5KB/s    eta 5s
-                                            76%[==================================================================>                      ] 168.00K  26.5KB/s    eta 2s     html body div div h2: 5 Conformance
html body div div h2: 6 Notation
html body div div h2: A References
-                                            90%[===============================================================================>         ] 200.00K  29.1KB/s    eta 2s     html body div div h2: B Definitions for Character Normalization
-                                           100%[========================================================================================>] 220.05K  32.1KB/s    in 6.9s

html body div div h2: C Expansion of Entity and Character References (Non-Normative)
html body div div h2: D Deterministic Content Models (Non-Normative)
html body div div h2: E Autodetection of Character Encodings (Non-Normative)
html body div div h2: F W3C XML Working Group (Non-Normative)
html body div div h2: G W3C XML Core Working Group (Non-Normative)
html body div div h2: H Production Notes (Non-Normative)
2019-10-23 17:31:34 (32.1 KB/s) - written to stdout [225335/225335]

html body div div h2: I Suggestions for XML Names (Non-Normative)
*/

func main() {
	decoder := xml.NewDecoder(os.Stdin)
	var stack []string // 元素名称的栈

	for {
		tok, err := decoder.Token()
		if err == io.EOF {
			break
		} else if err != nil {
			fmt.Fprintf(os.Stderr, "xmlselect: %v\n", err)
			os.Exit(1)
		}

		// 使用type switch
		switch tok := tok.(type) {
		case xml.StartElement:
			stack = append(stack, tok.Name.Local) // push
		case xml.EndElement:
			stack = stack[:len(stack)-1] // pop
		case xml.CharData:
			if containsAll(stack, os.Args[1:]) {
				fmt.Printf("%s: %s\n", strings.Join(stack, " "), tok)
			}
		}
	}
}

func containsAll(x, y []string) bool {
	for len(y) <= len(x) {
		if len(y) == 0 {
			return true
		}
		if x[0] == y[0] {
			y = y[1:]
		}
		x = x[1:]
	}
	return false
}
