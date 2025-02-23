package cmd

import (
	"github.com/spf13/cobra"
	"github.com/spf13/viper"
)

var (
	// Used for flags.
	userLicense string

	rootCmd = &cobra.Command{
		Use:   "corba",
		Short: "A short description of corba",
		Long:  `A long description of corba.`,
	}
)

func Execute() error {
	return rootCmd.Execute()
}

func init() {
	// setup flags of command
	rootCmd.PersistentFlags().StringP("author", "a", "zhoujiagen", "author name for copyright attribution")
	rootCmd.PersistentFlags().StringVarP(&userLicense, "license", "l", "", "name of license for the project")
	rootCmd.PersistentFlags().Bool("viper", true, "use Viper for configuration")

	// bind flags
	viper.BindPFlag("author", rootCmd.PersistentFlags().Lookup("author"))
	viper.BindPFlag("useViper", rootCmd.PersistentFlags().Lookup("viper"))
	// defaults
	viper.SetDefault("author", "zhoujiagen(zhoujiagen@gmail.com)")
	viper.SetDefault("license", "MIT")

	// register command
	rootCmd.AddCommand(addCmd)
	rootCmd.AddCommand(initCmd)
}
