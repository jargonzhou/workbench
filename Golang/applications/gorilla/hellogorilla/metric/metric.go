package metric

// Web度量值
type WebMetric struct {
	Status int
}

var MetricValue = &WebMetric{
	Status: 0,
}
