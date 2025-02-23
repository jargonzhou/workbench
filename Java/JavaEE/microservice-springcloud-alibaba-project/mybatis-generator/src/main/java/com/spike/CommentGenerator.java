package com.spike;

import org.mybatis.generator.api.IntrospectedColumn;
import org.mybatis.generator.api.IntrospectedTable;
import org.mybatis.generator.api.dom.java.*;
import org.mybatis.generator.internal.DefaultCommentGenerator;
import org.mybatis.generator.internal.util.StringUtility;

public class CommentGenerator extends DefaultCommentGenerator {
    private static final String EXAMPLE_SUFFIX = "Example";
    private static final String SCHEMA_FULL_CLASS_NAME = "io.swagger.v3.oas.annotations.media.Schema";
    private boolean addRemarkComments = true;

    /**
     * 给字段添加注释
     */
    @Override
    public void addFieldComment(Field field, IntrospectedTable introspectedTable,
                                IntrospectedColumn introspectedColumn) {
        String remarks = introspectedColumn.getRemarks();
        //根据参数和备注信息判断是否添加备注信息
        if (addRemarkComments && StringUtility.stringHasValue(remarks)) {
//            addFieldJavaDoc(field, remarks);
            //数据库中特殊字符需要转义
            if (remarks.contains("\"")) {
                remarks = remarks.replace("\"", "'");
            }
            //给model的字段添加swagger注解
            field.addJavaDocLine("@Schema(description = \"" + remarks + "\")");
        }
    }

    /**
     * 给model的字段添加注释
     */
    private void addFieldJavaDoc(Field field, String remarks) {
        //文档注释开始
        field.addJavaDocLine("/**");
        //获取数据库字段的备注信息
        String[] remarkLines = remarks.split(System.getProperty("line.separator"));
        for (String remarkLine : remarkLines) {
            field.addJavaDocLine(" * " + remarkLine);
        }
        addJavadocTag(field, false);
        field.addJavaDocLine(" */");
    }

    @Override
    public void addJavaFileComment(CompilationUnit compilationUnit) {
        super.addJavaFileComment(compilationUnit);
        //只在model中添加swagger注解类的导入
        if (!compilationUnit.getType().getFullyQualifiedName().contains(EXAMPLE_SUFFIX)) {
            compilationUnit.addImportedType(new FullyQualifiedJavaType(SCHEMA_FULL_CLASS_NAME));
            compilationUnit.addImportedType(new FullyQualifiedJavaType("lombok.Builder"));
            compilationUnit.addImportedType(new FullyQualifiedJavaType("lombok.NoArgsConstructor"));
            compilationUnit.addImportedType(new FullyQualifiedJavaType("lombok.AllArgsConstructor"));
        }
        //给Mapper添加@Repository注解，去除IDE错误提示
        if (compilationUnit.getType().getFullyQualifiedName().contains("Mapper") && compilationUnit instanceof Interface) {
            compilationUnit.addImportedType(new FullyQualifiedJavaType("org.springframework.stereotype.Repository"));
            ((Interface) compilationUnit).addAnnotation("@Repository");
        }
    }

    @Override
    public void addModelClassComment(TopLevelClass topLevelClass, IntrospectedTable introspectedTable) {
        topLevelClass.addJavaDocLine("@Builder");
        topLevelClass.addJavaDocLine("@NoArgsConstructor");
        topLevelClass.addJavaDocLine("@AllArgsConstructor");
        super.addModelClassComment(topLevelClass, introspectedTable);
    }
}