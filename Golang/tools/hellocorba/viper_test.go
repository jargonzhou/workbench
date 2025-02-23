package main

import (
	"testing"

	"github.com/spf13/viper"
)

/*
$ cat ~/.cobra_spike/spike.properties
a=1
b=2
c=3

*/
func TestViper(t *testing.T) {
	// Viper supports JSON, TOML, YAML, HCL, envfile and Java Properties files.
	viper.SetConfigName("spike")              // name of config file (without extension)
	viper.AddConfigPath("$HOME/.cobra_spike") // call multiple times to add many search paths
	viper.AddConfigPath(".")                  // optionally look for config in the working directory
	err := viper.ReadInConfig()               // Find and read the config file
	if err != nil {                           // Handle errors reading the config file
		t.Errorf("Fatal error config file: %s \n", err)
	}
	a := viper.GetInt("a")
	if a != 1 {
		t.Errorf("%d != 1", a)
	}

	// override
	viper.Set("a", 2)
	a = viper.GetInt("a")
	if a != 2 {
		t.Errorf("%d != 2", a)
	}
}
