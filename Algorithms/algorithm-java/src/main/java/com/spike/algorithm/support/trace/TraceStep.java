package com.spike.algorithm.support.trace;

public enum TraceStep {
        //# action2method = {
        //# 	'ns' : self.next_step,       # 下一步
        //# 	'an' : self.add_node,        # 添加节点
        //# 	'hn' : self.highlight_node,  # 高亮节点
        //# 	'ln' : self.label_node,      # 添加节点标签
        //# 	'un' : self.unlabel_node,    # 移除节点标签
        //# 	'rn' : self.remove_node,     # 删除节点
        //# 	'ae' : self.add_edge,        # 添加边
        //# 	'he' : self.highlight_edge,  # 高亮边
        //# 	'le' : self.label_edge,      # 添加边标签
        //# 	'ue' : self.unlabel_edge,    # 移除边标签
        //# 	're' : self.remove_edge,     # 删除边
        //# }
        //#
        //# https://github.com/mapio/GraphvizAnim/blob/master/gvanim/__main__.py
        ns,
        an,
        hn,
        ln,
        un,
        rn,
        ae,
        he,
        le,
        ue,
        re
    }
