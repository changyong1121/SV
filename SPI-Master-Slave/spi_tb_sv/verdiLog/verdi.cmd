wvCreateWindow
wvOpenFile -win $_nWave2 \
           {/home/user08/training/ww04/SPI-Master-Slave/spi_tb_sv/fsdbdump.fsdb}
verdiWindowResize -win $_Verdi_1 "510" "153" "900" "700"
verdiSetActWin -win $_nWave2
verdiWindowResize -win $_Verdi_1 "510" "153" "900" "700"
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
verdiSetActWin -dock widgetDock_<Inst._Tree>
verdiDockWidgetSetCurTab -dock widgetDock_<Decl._Tree>
verdiSetActWin -dock widgetDock_<Decl._Tree>
verdiDockWidgetSetCurTab -dock widgetDock_<Inst._Tree>
verdiSetActWin -dock widgetDock_<Inst._Tree>
debExit
