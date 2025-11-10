import { Github, Heart } from "lucide-react";

const Footer = () => {
  return (
    <footer className="bg-secondary border-t border-border mt-20">
      <div className="container mx-auto px-4 py-8">
        <div className="flex flex-col md:flex-row items-center justify-between gap-4">
          <div className="flex items-center gap-2 text-sm text-muted-foreground">
            <span>Powered by EDA Playground</span>
            <span>•</span>
            <span>Built by the CDF Open Education Team</span>
            <span>•</span>
            <span className="flex items-center gap-1">
              100% Open Source
              <Heart className="w-3 h-3 fill-destructive text-destructive" />
            </span>
          </div>
          <a
            href="https://github.com/chiplearn"
            target="_blank"
            rel="noopener noreferrer"
            className="flex items-center gap-2 text-sm text-muted-foreground hover:text-accent transition-colors"
          >
            <Github className="w-4 h-4" />
            Contribute on GitHub
          </a>
        </div>
      </div>
    </footer>
  );
};

export default Footer;
