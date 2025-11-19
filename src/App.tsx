import { Toaster } from "@/components/ui/toaster";
import { Toaster as Sonner } from "@/components/ui/sonner";
import { TooltipProvider } from "@/components/ui/tooltip";
import { QueryClient, QueryClientProvider } from "@tanstack/react-query";
import { BrowserRouter, Routes, Route } from "react-router-dom";
import Layout from "./components/Layout";
import Home from "./pages/Home";
import Modules from "./pages/Modules";
import VerilogModules from "./pages/VerilogModules";
import SystemVerilogModules from "./pages/SystemVerilogModules";
import UVMModules from "./pages/UVMModules";
import ModuleDetail from "./pages/ModuleDetail";
import Visualizer from "./pages/Visualizer";
import Community from "./pages/Community";
import About from "./pages/About";
import NotFound from "./pages/NotFound";

const queryClient = new QueryClient();

const App = () => (
  <QueryClientProvider client={queryClient}>
    <TooltipProvider>
      <Toaster />
      <Sonner />
      <BrowserRouter>
        <Layout>
          <Routes>
            <Route path="/" element={<Home />} />
            <Route path="/modules" element={<Modules />} />
            <Route path="/verilog-modules" element={<VerilogModules />} />
            <Route path="/systemverilog-modules" element={<SystemVerilogModules />} />
            <Route path="/uvm-modules" element={<UVMModules />} />
            <Route path="/modules/:slug" element={<ModuleDetail />} />
            <Route path="/visualizer" element={<Visualizer />} />
            <Route path="/community" element={<Community />} />
            <Route path="/about" element={<About />} />
            {/* ADD ALL CUSTOM ROUTES ABOVE THE CATCH-ALL "*" ROUTE */}
            <Route path="*" element={<NotFound />} />
          </Routes>
        </Layout>
      </BrowserRouter>
    </TooltipProvider>
  </QueryClientProvider>
);

export default App;
