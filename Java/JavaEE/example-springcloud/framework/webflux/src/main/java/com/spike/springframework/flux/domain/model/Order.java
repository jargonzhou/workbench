package com.spike.springframework.flux.domain.model;

import org.springframework.data.annotation.CreatedDate;
import org.springframework.data.annotation.Id;
import org.springframework.data.annotation.LastModifiedDate;
import org.springframework.data.annotation.Version;
import org.springframework.data.relational.core.mapping.Table;

import java.math.BigDecimal;
import java.time.Instant;

@Table("orders") // 表名称
public record Order(
        @Id
        Long id,

        String bookIsbn,
        String bookName,
        BigDecimal bookPrice,
        Integer quantity,
        OrderStatus status,

        @CreatedDate
        Instant createdDate,
        @LastModifiedDate
        Instant lastModifiedDate,

        @Version
        int version
) {
    public static Order of(String bookIsbn, String bookName, BigDecimal bookPrice,
                           Integer quantity, OrderStatus status) {
        return new Order(null, bookIsbn, bookName, bookPrice, quantity, status,
                null, null, 0);
    }
}
