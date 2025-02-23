package cmd

import (
	"fmt"

	"github.com/spf13/cobra"
)

var (
	SpikeVersion string = "0.1"
)

func init() {
	// register command
	rootCmd.AddCommand(versionCmd)
}

var versionCmd = &cobra.Command{
	Use:   "version",
	Short: "Short description of version",
	Long:  "Long description of version",
	Run: func(cmd *cobra.Command, args []string) {
		fmt.Printf("Spike version: %s\n", SpikeVersion)
	},
}
