package cmd

import (
	"fmt"
	"strings"

	"github.com/spf13/cobra"
)

var addCmd = &cobra.Command{
	Use:   "add",
	Short: "Short description of add",
	Long:  "Long description of add",
	Run: func(cmd *cobra.Command, args []string) {
		fmt.Printf("Spike add: %s\n", strings.Join(args, " "))
	},
}
