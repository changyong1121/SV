simSetSimulator "-vcssv" -exec \
           "/home/user08/training/ww04/SV/uvm_zw/spi/sim/spi_simv" -args \
           "+UVM_NO_RELNOTES -cm line+tgl+cond+fsm+branch+assert -assert summary"
debImport "-dbdir" "/home/user08/training/ww04/SV/uvm_zw/spi/sim/spi_simv.daidir"
debLoadSimResult /home/user08/training/ww04/SV/uvm_zw/spi/sim/spi_sim.fsdb
wvCreateWindow
verdiSetActWin -win $_nWave2
verdiWindowResize -win $_Verdi_1 "0" "27" "1920" "1016"
verdiWindowResize -win $_Verdi_1 "0" "27" "1920" "1016"
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcHBSelect "spi_tb.spi_if" -win $_nTrace1
srcSetScope "spi_tb.spi_if" -delim "." -win $_nTrace1
srcHBSelect "spi_tb.spi_if" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
verdiSetActWin -dock widgetDock_<Signal_List>
srcSignalViewSelect "spi_tb.spi_if.rx_data\[7:0\]"
srcSignalViewSelect "spi_tb.spi_if.tx_data\[7:0\]" "spi_tb.spi_if.start" \
           "spi_tb.spi_if.clk" "spi_tb.spi_if.rst_n" \
           "spi_tb.spi_if.rx_data\[7:0\]"
wvAddSignal -win $_nWave2 "/spi_tb/spi_if/tx_data\[7:0\]" "/spi_tb/spi_if/start" \
           "/spi_tb/spi_if/clk" "/spi_tb/spi_if/rst_n" \
           "/spi_tb/spi_if/rx_data\[7:0\]"
wvSetPosition -win $_nWave2 {("G1" 0)}
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetCursor -win $_nWave2 55987.747451 -snap {("G1" 2)}
verdiSetActWin -win $_nWave2
verdiSetActWin -dock widgetDock_<Signal_List>
wvSetCursor -win $_nWave2 111560.770846 -snap {("G1" 3)}
verdiSetActWin -win $_nWave2
wvSetCursor -win $_nWave2 97874.877025 -snap {("G1" 5)}
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
srcHBSelect "spi_tb" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect "spi_tb" -win $_nTrace1
srcSetScope "spi_tb" -delim "." -win $_nTrace1
srcHBSelect "spi_tb" -win $_nTrace1
srcHBSelect "spi_tb.unnamed\$\$_1" -win $_nTrace1
srcSetScope "spi_tb.unnamed\$\$_1" -delim "." -win $_nTrace1
srcHBSelect "spi_tb.unnamed\$\$_1" -win $_nTrace1
srcHBSelect "spi_tb.unnamed\$\$_0" -win $_nTrace1
srcSetScope "spi_tb.unnamed\$\$_0" -delim "." -win $_nTrace1
srcHBSelect "spi_tb.unnamed\$\$_0" -win $_nTrace1
srcHBSelect "spi_tb.unnamed\$\$_1" -win $_nTrace1
srcSetScope "spi_tb.unnamed\$\$_1" -delim "." -win $_nTrace1
srcHBSelect "spi_tb.unnamed\$\$_1" -win $_nTrace1
srcHBSelect "spi_tb.spi_slv_if" -win $_nTrace1
srcSetScope "spi_tb.spi_slv_if" -delim "." -win $_nTrace1
srcHBSelect "spi_tb.spi_slv_if" -win $_nTrace1
wvSetCursor -win $_nWave2 56402.471506 -snap {("G1" 1)}
verdiSetActWin -win $_nWave2
srcSignalViewSelect "spi_tb.spi_slv_if.rst_n"
srcSignalViewSelect "spi_tb.spi_slv_if.rst_n"
verdiSetActWin -dock widgetDock_<Signal_List>
wvSetPosition -win $_nWave2 {("G1" 0)}
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 1)}
wvAddSignal -win $_nWave2 "/spi_tb/spi_slv_if/rst_n"
wvSetPosition -win $_nWave2 {("G1" 1)}
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSelectSignal -win $_nWave2 {( "G1" 2 )} 
verdiSetActWin -win $_nWave2
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 1)}
srcHBSelect "spi_tb.dut" -win $_nTrace1
srcSetScope "spi_tb.dut" -delim "." -win $_nTrace1
srcHBSelect "spi_tb.dut" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect "spi_tb.spi_if" -win $_nTrace1
srcSetScope "spi_tb.spi_if" -delim "." -win $_nTrace1
srcHBSelect "spi_tb.spi_if" -win $_nTrace1
srcHBSelect "spi_tb" -win $_nTrace1
srcHBSelect "spi_tb" -win $_nTrace1
srcSetScope "spi_tb" -delim "." -win $_nTrace1
srcHBSelect "spi_tb" -win $_nTrace1
srcHBSelect "spi_tb.spi_if" -win $_nTrace1
srcSetScope "spi_tb.spi_if" -delim "." -win $_nTrace1
srcHBSelect "spi_tb.spi_if" -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "rst_n" -line 5 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvSetPosition -win $_nWave2 {("G1" 0)}
wvSetPosition -win $_nWave2 {("G1" 1)}
wvAddSignal -win $_nWave2 "/spi_tb/spi_if/rst_n"
wvSetPosition -win $_nWave2 {("G1" 1)}
wvSetPosition -win $_nWave2 {("G1" 2)}
srcHBSelect "spi_tb.spi_slv_if" -win $_nTrace1
srcSetScope "spi_tb.spi_slv_if" -delim "." -win $_nTrace1
srcHBSelect "spi_tb.spi_slv_if" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
wvSetCursor -win $_nWave2 57646.643671 -snap {("G1" 3)}
verdiSetActWin -win $_nWave2
wvGoToTime -win $_nWave2 725000
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoom -win $_nWave2 228927.678464 2511568.878224
debReload
wvSetCursor -win $_nWave2 1147735.263970 -snap {("G1" 5)}
wvZoomAll -win $_nWave2
srcHBSelect "spi_tb.dut" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect "spi_tb.dut" -win $_nTrace1
srcSetScope "spi_tb.dut" -delim "." -win $_nTrace1
srcHBSelect "spi_tb.dut" -win $_nTrace1
srcHBSelect "spi_tb" -win $_nTrace1
srcSetScope "spi_tb" -delim "." -win $_nTrace1
srcHBSelect "spi_tb" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Signal_List>
srcDeselectAll -win $_nTrace1
srcSelect -win $_nTrace1 -signal "spi_if.rx_data" -line 22 -pos 1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvSetPosition -win $_nWave2 {("G1" 1)}
wvAddSignal -win $_nWave2 "/spi_tb/spi_if/rx_data\[7:0\]"
wvSetPosition -win $_nWave2 {("G1" 1)}
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetCursor -win $_nWave2 2169006.808638 -snap {("G1" 5)}
wvZoomAll -win $_nWave2
verdiSetActWin -win $_nWave2
wvSetCursor -win $_nWave2 2397105.038992 -snap {("G1" 3)}
wvZoomAll -win $_nWave2
wvZoomAll -win $_nWave2
wvZoomAll -win $_nWave2
wvZoomAll -win $_nWave2
wvZoomAll -win $_nWave2
wvZoomAll -win $_nWave2
wvZoomAll -win $_nWave2
wvSelectSignal -win $_nWave2 {( "G1" 2 )} 
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 1)}
srcHBSelect "spi_tb.spi_slv_if" -win $_nTrace1
srcSetScope "spi_tb.spi_slv_if" -delim "." -win $_nTrace1
srcHBSelect "spi_tb.spi_slv_if" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
srcSelect -signal "slave_rx_data" -line 14 -pos 1 -win $_nTrace1
srcDeselectAll -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "slave_tx_data" -line 15 -pos 1 -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "slave_rx_data" -line 14 -pos 1 -win $_nTrace1
wvSetPosition -win $_nWave2 {("G1" 0)}
wvSetPosition -win $_nWave2 {("G1" 4)}
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetPosition -win $_nWave2 {("G1" 6)}
wvSetPosition -win $_nWave2 {("G2" 0)}
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G2" 0)}
wvAddSignal -win $_nWave2 "/spi_tb/spi_slv_if/slave_rx_data\[7:0\]"
wvSetPosition -win $_nWave2 {("G2" 0)}
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSetCursor -win $_nWave2 1144638.392322 -snap {("G2" 1)}
verdiSetActWin -win $_nWave2
wvZoomAll -win $_nWave2
srcDeselectAll -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "slave_tx_data" -line 15 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcSelect -win $_nTrace1 -range {15 15 10 10 9 10}
srcDeselectAll -win $_nTrace1
srcSelect -signal "slave_tx_data" -line 15 -pos 1 -win $_nTrace1
srcSelect -win $_nTrace1 -range {15 23 10 1 11 1}
srcDeselectAll -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "slave_tx_data" -line 15 -pos 1 -win $_nTrace1
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G3" 0)}
wvAddSignal -win $_nWave2 "/spi_tb/spi_slv_if/slave_tx_data\[7:0\]"
wvSetPosition -win $_nWave2 {("G3" 0)}
wvSetPosition -win $_nWave2 {("G3" 1)}
wvSetPosition -win $_nWave2 {("G3" 1)}
wvSelectSignal -win $_nWave2 {( "G3" 1 )} 
verdiSetActWin -win $_nWave2
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G4" 0)}
wvSetPosition -win $_nWave2 {("G3" 0)}
wvZoom -win $_nWave2 136858.938212 2546405.698860
wvSetCursor -win $_nWave2 472200.778926 -snap {("G1" 5)}
wvZoomAll -win $_nWave2
wvSetCursor -win $_nWave2 290306.838632 -snap {("G1" 1)}
wvSetCursor -win $_nWave2 6225008.068386 -snap {("G1" 3)}
wvZoom -win $_nWave2 904098.440312 3587363.077385
debReload
wvCenterMarker -win $_nWave2
wvGoToTime -win $_nWave2 10500
wvGoToTime -win $_nWave2 105000
wvZoom -win $_nWave2 20925.279113 399189.940008
wvZoom -win $_nWave2 69711.663092 205632.797991
wvZoom -win $_nWave2 99880.121348 137223.780486
wvZoom -win $_nWave2 100820.993384 112111.457814
debReload
wvSetCursor -win $_nWave2 103028.966632 -snap {("G1" 1)}
wvZoomAll -win $_nWave2
wvZoom -win $_nWave2 41472.405519 655264.007199
wvZoom -win $_nWave2 49572.834575 197221.564193
srcSignalViewSelect "spi_tb.spi_slv_if.sclk"
srcSignalViewSelect "spi_tb.spi_slv_if.sclk"
verdiSetActWin -dock widgetDock_<Signal_List>
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 3)}
wvSetPosition -win $_nWave2 {("G1" 4)}
wvAddSignal -win $_nWave2 "/spi_tb/spi_slv_if/sclk"
wvSetPosition -win $_nWave2 {("G1" 4)}
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSelectSignal -win $_nWave2 {( "G1" 5 )} 
verdiSetActWin -win $_nWave2
wvCut -win $_nWave2
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetPosition -win $_nWave2 {("G1" 4)}
srcHBSelect "spi_tb.spi_if" -win $_nTrace1
srcSetScope "spi_tb.spi_if" -delim "." -win $_nTrace1
srcHBSelect "spi_tb.spi_if" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcSignalViewSelect "spi_tb.spi_if.sclk"
srcSignalViewSelect "spi_tb.spi_if.sclk"
wvSetPosition -win $_nWave2 {("G1" 0)}
wvSetPosition -win $_nWave2 {("G1" 1)}
verdiSetActWin -dock widgetDock_<Signal_List>
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 3)}
wvSetPosition -win $_nWave2 {("G1" 4)}
wvAddSignal -win $_nWave2 "/spi_tb/spi_if/sclk"
wvSetPosition -win $_nWave2 {("G1" 4)}
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetCursor -win $_nWave2 144698.650778 -snap {("G1" 5)}
verdiSetActWin -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
srcHBSelect "spi_tb" -win $_nTrace1
srcHBSelect "spi_tb" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcSetScope "spi_tb" -delim "." -win $_nTrace1
srcHBSelect "spi_tb" -win $_nTrace1
srcSignalViewSelect "spi_tb.slave_reset_response\[31:0\]"
verdiSetActWin -dock widgetDock_<Signal_List>
srcDeselectAll -win $_nTrace1
srcSelect -win $_nTrace1 -signal "spi_if.sclk" -line 42 -pos 1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcHBSelect "spi_tb.dut" -win $_nTrace1
srcSetScope "spi_tb.dut" -delim "." -win $_nTrace1
srcHBSelect "spi_tb.dut" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcSignalViewSelect "spi_tb.dut.start"
srcSignalViewSelect "spi_tb.dut.tx_data\[7:0\]"
verdiSetActWin -dock widgetDock_<Signal_List>
srcSignalViewSelect "spi_tb.dut.tx_data\[7:0\]" "spi_tb.dut.rx_data\[7:0\]"
wvSetPosition -win $_nWave2 {("G1" 1)}
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 3)}
wvAddSignal -win $_nWave2 "/spi_tb/dut/tx_data\[7:0\]" \
           "/spi_tb/dut/rx_data\[7:0\]"
wvSetPosition -win $_nWave2 {("G1" 3)}
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetCursor -win $_nWave2 140297.293171 -snap {("G1" 5)}
wvZoomAll -win $_nWave2
verdiSetActWin -win $_nWave2
wvSetCursor -win $_nWave2 734061.577684 -snap {("G1" 4)}
wvZoom -win $_nWave2 559877.474505 1799902.399520
srcSignalViewSelect "spi_tb.dut.done"
srcSignalViewSelect "spi_tb.dut.done"
verdiSetActWin -dock widgetDock_<Signal_List>
srcSignalViewSelect "spi_tb.dut.busy" "spi_tb.dut.done"
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetPosition -win $_nWave2 {("G1" 6)}
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetPosition -win $_nWave2 {("G1" 4)}
wvSetPosition -win $_nWave2 {("G1" 3)}
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 3)}
wvSetPosition -win $_nWave2 {("G1" 4)}
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetPosition -win $_nWave2 {("G1" 6)}
wvSetPosition -win $_nWave2 {("G1" 7)}
wvAddSignal -win $_nWave2 "/spi_tb/dut/busy" "/spi_tb/dut/done"
wvSetPosition -win $_nWave2 {("G1" 7)}
wvSetPosition -win $_nWave2 {("G1" 9)}
wvSetCursor -win $_nWave2 706672.872684 -snap {("G1" 9)}
verdiSetActWin -win $_nWave2
wvSetCursor -win $_nWave2 102653.533085 -snap {("G2" 1)}
wvSetCursor -win $_nWave2 1184978.827564 -snap {("G1" 1)}
wvSetCursor -win $_nWave2 789925.028111 -snap {("G2" 1)}
