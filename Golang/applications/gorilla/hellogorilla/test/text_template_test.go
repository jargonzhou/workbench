package test

import (
	"os"
	"testing"
	"text/template"

	"hellogorilla/domain"
)

// 简单对象
func _TestTemplate(t *testing.T) {
	var tmpl = `Note - Id: {{.Id}}, Title: {{.Title}}, Description: {{.Description}}`
	note := domain.Note{Id: 1, Title: "一个笔记", Description: "笔记内容"}

	tp := template.New("note")

	tp, err := tp.Parse(tmpl)
	if err != nil {
		t.Fatal("Parse: ", err)
	}

	if err := tp.Execute(os.Stdout, note); err != nil {
		t.Fatal("Execute: ", err)
	}
}

// range指令: 一组对象
func _TestRange(t *testing.T) {
	var tmpl = `Notes are:
{{range .}}
	Id: {{.Id}}, Title: {{.Title}}, Description: {{.Description}}
{{end}}`

	notes := []domain.Note{
		{Id: 1, Title: "text/template", Description: "textual output"},
		{Id: 2, Title: "html/template", Description: "HTML output"},
	}
	tp := template.New("note")
	tp, err := tp.Parse(tmpl)
	if err != nil {
		t.Fatal("Parse: ", err)
	}

	if err := tp.Execute(os.Stdout, notes); err != nil {
		t.Fatal("Execute: ", err)
	}
}

// 命名的参数
func _TestNamedTemplate(t *testing.T) {
	tp, err := template.New("test").Parse(`{{define "T"}}Hello, {{.}}!{{end}}`)
	err = tp.ExecuteTemplate(os.Stdout, "T", "World")
	if err != nil {
		t.Fatal("Execute: ", err)
	}

	tp, err = template.New("test").Parse(`{{define "T"}}Hello, {{.Id}}-{{.Title}}-{{.Description}}!{{end}}`)
	note := domain.Note{Id: 1, Title: "一个笔记", Description: "笔记内容"}
	err = tp.ExecuteTemplate(os.Stdout, "T", note)
	if err != nil {
		t.Fatal("Execute: ", err)
	}
}

// 变量
func _TestVariable(t *testing.T) {
	var tmpl = `
{{ $note := "一个笔记" }}
{{ $note }}`

	tp := template.New("note")
	tp, err := tp.Parse(tmpl)
	if err != nil {
		t.Fatal("Parse: ", err)
	}

	if err := tp.Execute(os.Stdout, nil); err != nil {
		t.Fatal("Execute: ", err)
	}
}

func TestPipe(t *testing.T) {
	var tmpl = `
	{{ $a := 1 }}
	{{ $b := 1 }}
	{{ if eq $a $b }} a and b are {{ else }} not {{ end }} equal
	`

	tp := template.New("pipe")
	tp, err := tp.Parse(tmpl)
	if err != nil {
		t.Fatal("Parse: ", err)
	}

	if err := tp.Execute(os.Stdout, nil); err != nil {
		t.Fatal("Execute: ", err)
	}
}
