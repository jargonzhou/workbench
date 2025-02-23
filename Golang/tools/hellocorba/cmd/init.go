package cmd

import (
	"fmt"
	"os"
	"strings"

	homedir "github.com/mitchellh/go-homedir"
	"github.com/spf13/cobra"
	"github.com/spf13/viper"
)

// Used for flags.
var cfgFile string

var initCmd = &cobra.Command{
	Use:   "init",
	Short: "Short description of init",
	Long:  "Long description of init",
	Run: func(cmd *cobra.Command, args []string) {
		fmt.Printf("Spike init: args=%s, configFile=%s\n",
			strings.Join(args, " "), viper.ConfigFileUsed())
	},
}

func init() {
	// specify initialize function
	cobra.OnInitialize(initConfig)

	// setup flags of command
	initCmd.PersistentFlags().StringVar(&cfgFile, "config", "", "config file (default is $HOME/.cobra.yaml)")
}

func initConfig() {
	if cfgFile != "" {
		// Use config file from the flag.
		viper.SetConfigFile(cfgFile)
	} else {
		// Find home directory.
		home, err := homedir.Dir()
		if err != nil {
			fmt.Errorf("homedir error: %v", err)
			os.Exit(1)
		}

		// Search config in home directory with name ".cobra" (without extension).
		viper.AddConfigPath(home)
		viper.SetConfigName(".cobra")
	}

	viper.AutomaticEnv()

	err := viper.ReadInConfig()
	if err == nil {
		fmt.Println("Using config file: ", viper.ConfigFileUsed())
	} else {
		if _, ok := err.(viper.ConfigFileNotFoundError); ok {
			fmt.Printf("%v\n", err)
		} else {
			fmt.Printf("Read Config file failed: %v\n", err)
		}
	}
}
